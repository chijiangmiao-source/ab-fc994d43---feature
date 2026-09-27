"""有限精化预算下的分支跟踪分区(trace partitioning)不动点引擎。

与单分区引擎(app.analyzer)语义一致,区别在于:每个程序点最多保留 budget
个**互不混淆的分支八边形状态**。分区键是最近 w 个比较分支抉择的稳定编码
(w = budget - 1):

    token = (分支指令编号, 方向)        方向 ∈ {"t"(真), "f"(假)}
    key   = (token, ...)                至多 w 个,更旧抉择在队首截断
    key ()= "root":尚未区分任何分支的状态

每个槽位(partition slot)独立经历:
  * 回边目标处的固定规则 widening(上升迭代,混沌工作集);
  * 下降复算(Gauss-Seidel 重算取交,回收 widening 损失的精度);
  * 终态逐条转移校验 f(inv[p,s]) ⊑ inv[q,t]。

预算耗尽时**只合并不丢弃**:每个点维护单调增长的别名表(完整键 → 槽位),
新键到来而槽位已满时,固定并入键序最小的既有槽位(八边形凸包);别名表
一旦登记不再改变,槽位身份稳定,widening 终止性与单分区情形相同。循环内
更旧的分支抉择由长度为 w 的历史窗口确定性截断,同样是凸包合流。任何可达
执行至少落在某个保留槽位中(整体仍为上近似)。

断言放行条件:该程序点上**全部**可达槽位各自蕴含包线。
"""
from __future__ import annotations

from collections import deque

from .octagon import Octagon
from .transfers import apply_action, check_assertion

MAX_DESCENDING_PASSES = 8
MAX_BUDGET = 8

# 合并原因(固定规则,响应中原样给出)
REASON_BUDGET = "budget_exhausted_merge_into_min_key"
REASON_WINDOW = "history_window_truncation"


def parse_refinement(raw) -> "(int | None, list)":
    """解析可选 refinement 字段。

    返回 (budget, errors):budget 为 None 表示未选择精化(走兼容路径);
    budget == 1 同样走原引擎(严格兼容)。结构问题收集为合并错误。
    """
    if raw is None:
        return None, []
    if not isinstance(raw, dict):
        return None, [{"kind": "invalid_refinement",
                       "detail": "'refinement' must be an object"}]
    if "budget" not in raw:
        return None, []
    budget = raw["budget"]
    if isinstance(budget, bool) or not isinstance(budget, int):
        return None, [{"kind": "invalid_refinement",
                       "detail": "'refinement.budget' must be an integer"}]
    if not (1 <= budget <= MAX_BUDGET):
        return None, [{"kind": "invalid_refinement",
                       "detail": f"'refinement.budget' must be within 1..{MAX_BUDGET}",
                       "value": budget}]
    return budget, []


# ----------------------------------------------------------------------
# 分区键工具
# ----------------------------------------------------------------------
def extend_key(key: tuple, token: tuple, window: int) -> "(tuple, bool)":
    """记录一个分支抉择;窗口超限时截断最旧抉择(确定性合流)。

    返回 (新键, 是否发生截断)。
    """
    if window <= 0:
        return (), True
    new = key + (token,)
    if len(new) > window:
        return new[-window:], True
    return new, False


def render_key(key: tuple) -> list:
    """槽位键的机器可读形式:[{"branch": id, "direction": "true"/"false"}, ...]。"""
    return [{"branch": br, "direction": ("true" if d == "t" else "false")}
            for br, d in key]


def key_text(key: tuple) -> str:
    if not key:
        return "root"
    return ",".join(f"b{br}={'t' if d == 't' else 'f'}" for br, d in key)


# ----------------------------------------------------------------------
# 分区引擎
# ----------------------------------------------------------------------
class PartitionedEngine:
    def __init__(self, prog, budget: int):
        self.prog = prog
        self.points = prog.points
        self.budget = budget
        self.window = budget - 1
        # inv[p] = {slot_key: Octagon};缺省即该槽不可达
        self.inv = {p: {} for p in self.points}
        # groups[p] = {完整目标键: 槽位键};单调增长的别名表
        self.groups = {p: {} for p in self.points}
        self.in_edges = {p: [] for p in self.points}
        self.out_edges = {p: [] for p in self.points}
        for e in prog.edges:
            self.out_edges[e.src].append(e)
            self.in_edges[e.dst].append(e)
        self.initial = self._initial_state()
        self.ascending_iterations = 0
        self.descending_passes = 0
        # 合并台账(预算溢出按完整键自然去重;窗口截断按 (点,边) 去重)
        self.merge_log = []
        self._window_seen = set()

    def _initial_state(self) -> Octagon:
        o = Octagon(self.prog.nregs)
        n = self.prog.nregs
        for i, (lo, hi) in enumerate(self.prog.initial):
            if hi is not None:
                o.m[i][n + i] = 2 * hi
            if lo is not None:
                o.m[n + i][i] = -2 * lo
        o.close()
        return o

    # ------------------------------------------------------------------
    # 键映射与固定规则合并
    # ------------------------------------------------------------------
    def _dest_full_key(self, key: tuple, edge) -> "(tuple, bool)":
        """沿一条边后的完整目标键;非分支边键不变,分支边追加抉择。"""
        if edge.kind == "branch_true":
            return extend_key(key, (edge.src, "t"), self.window)
        if edge.kind == "branch_false":
            return extend_key(key, (edge.src, "f"), self.window)
        return key, False

    def _resolve(self, point, full_key: tuple, edge=None) -> tuple:
        """完整键 → 稳定槽位;槽位满且为新键时固定并入最小槽位(不丢弃)。"""
        aliases = self.groups[point]
        slot = aliases.get(full_key)
        if slot is not None:
            return slot
        buckets = self.inv[point]
        if len(buckets) < self.budget:
            aliases[full_key] = full_key
            buckets[full_key] = None  # 占位:由调用方填入;None 槽位等同不可达
            return full_key
        min_slot = min(buckets)
        aliases[full_key] = min_slot
        self.merge_log.append({
            "point": point,
            "reason": REASON_BUDGET,
            "surviving_key": render_key(min_slot),
            "merged_key": render_key(full_key),
            "edge": (None if edge is None else
                     {"from": edge.src, "to": edge.dst, "kind": edge.kind}),
        })
        return min_slot

    def _note_window(self, point, edge) -> None:
        tag = (point, edge.src, edge.kind)
        if tag not in self._window_seen:
            self._window_seen.add(tag)
            self.merge_log.append({
                "point": point,
                "reason": REASON_WINDOW,
                "history_window": self.window,
                "edge": {"from": edge.src, "to": edge.dst, "kind": edge.kind},
            })

    # ------------------------------------------------------------------
    # 上升迭代:逐槽位工作集,回边目标处逐槽 widening
    # ------------------------------------------------------------------
    def _ascending(self) -> None:
        inv = self.inv
        groups = self.groups
        inv[0][()] = self.initial
        groups[0][()] = ()
        widen_at = self.prog.widening_points
        work = deque([(0, ())])
        in_work = {(0, ())}
        while work:
            p, slot = work.popleft()
            in_work.discard((p, slot))
            src = inv.get(p, {}).get(slot)
            if src is None:
                continue
            for e in self.out_edges[p]:
                y = apply_action(src, e.action)
                if y is None:
                    continue
                q = e.dst
                full, truncated = self._dest_full_key(slot, e)
                target = self._resolve(q, full, e)
                if truncated:
                    self._note_window(q, e)
                old = inv[q][target]
                if old is None:
                    inv[q][target] = y
                else:
                    joined = old.join(y)
                    if joined.incl(old):
                        continue
                    inv[q][target] = old.widen(joined) if q in widen_at else joined
                item = (q, target)
                if item not in in_work:
                    work.append(item)
                    in_work.add(item)
                self.ascending_iterations += 1
        # 清理上升期遗留的 None 占位(从未被填充的槽位)及其悬空别名,
        # 保持 groups 像集恰为现存槽位,供下降复算与终态校验使用。
        for p in self.points:
            dead = [k for k, v in inv[p].items() if v is None]
            for k in dead:
                del inv[p][k]
            if dead:
                for fk, slot in list(groups[p].items()):
                    if slot in dead:
                        del groups[p][fk]

    # ------------------------------------------------------------------
    # 下降复算:别名表固定后逐槽位重算入边贡献并取交
    # ------------------------------------------------------------------
    def _slot_contributions(self, q) -> dict:
        """汇总一个点上每个槽位本轮的入边迁移贡献(同源凸包)。"""
        contribs = {}
        if q == 0:
            contribs[()] = self.initial.copy()
        for e in self.in_edges[q]:
            for sk, sv in self.inv[e.src].items():
                y = apply_action(sv, e.action)
                if y is None:
                    continue
                full, _ = self._dest_full_key(sk, e)
                target = self.groups[q].get(full)
                if target is None:  # 防御:下降只可能更不可行,不应出现新键
                    target = self._resolve(q, full, e)
                if target in contribs:
                    contribs[target] = contribs[target].join(y)
                else:
                    contribs[target] = y
        return contribs

    def _descending(self) -> None:
        inv = self.inv
        groups = self.groups
        for _ in range(MAX_DESCENDING_PASSES):
            # 快照上一个归纳后不动点(含别名表):本轮加强若破坏归纳性须整体回退
            snap_inv = {p: dict(v) for p, v in inv.items()}
            snap_groups = {p: dict(v) for p, v in groups.items()}
            changed = False
            for q in self.points:
                cur = inv[q]
                if not cur:
                    continue
                contribs = self._slot_contributions(q)
                new_state = {}
                for slot, val in contribs.items():
                    if slot in cur:
                        tightened = val.meet_with(cur[slot])
                        if tightened.empty:
                            changed = True  # 该槽位在更强不变量下不再可达
                            continue
                        new_state[slot] = tightened
                    else:
                        new_state[slot] = val
                # 本轮无入边贡献的槽位:与单分区引擎一致,保持旧值不擅判死亡
                for slot in cur:
                    if slot not in contribs:
                        new_state[slot] = cur[slot]
                dead = cur.keys() - new_state.keys()
                if dead:
                    for fk in list(groups[q]):
                        if groups[q][fk] in dead:
                            del groups[q][fk]
                if set(new_state) != set(cur) or any(
                        not (new_state[s].incl(cur[s]) and cur[s].incl(new_state[s]))
                        for s in new_state if s in cur):
                    changed = True
                inv[q] = new_state
            self.descending_passes += 1
            if not changed:
                break
            # 只在候选确为归纳后不动点时提交,否则回退到上一归纳不动点并终止
            if self._inductive_violations(inv):
                for p in self.points:
                    inv[p] = snap_inv[p]
                    groups[p] = snap_groups[p]
                break

    # ------------------------------------------------------------------
    # 终态校验:逐槽位、逐转移显式复核
    # ------------------------------------------------------------------
    def _inductive_violations(self, states: dict) -> list:
        """检查 states 是否为逐槽位归纳后不动点。"""
        violations = []
        head = states[0].get(())
        if head is None or not self.initial.incl(head):
            violations.append({"from": "entry", "to": 0, "kind": "entry", "partition": []})
        for p in self.points:
            for slot, src in states[p].items():
                for e in self.out_edges[p]:
                    y = apply_action(src, e.action)
                    if y is None:
                        continue
                    full, _ = self._dest_full_key(slot, e)
                    target = self.groups[e.dst].get(full)
                    dst = states[e.dst].get(target) if target is not None else None
                    if dst is None or not y.incl(dst):
                        violations.append({
                            "from": p, "to": e.dst, "kind": e.kind,
                            "partition": render_key(slot),
                            "target_partition": render_key(full),
                        })
        return violations

    def _verify(self) -> list:
        return self._inductive_violations(self.inv)

    def run(self) -> list:
        self._ascending()
        self._descending()
        return self._verify()

    # ------------------------------------------------------------------
    # 证据装配:每个槽位的入边来源(调用方可据此重放入边与转移)
    # ------------------------------------------------------------------
    def slot_incoming(self, q) -> dict:
        """返回 {槽位键: [{"from","from_partition","edge"}, ...]}(终态下可行的来源)。"""
        sources = {}
        if q == 0:
            sources[()] = [{"from": "entry", "from_partition": [], "edge": "entry"}]
        for e in self.in_edges[q]:
            for sk, sv in self.inv[e.src].items():
                y = apply_action(sv, e.action)
                if y is None:
                    continue
                full, _ = self._dest_full_key(sk, e)
                target = self.groups[q].get(full)
                if target is None:
                    continue
                sources.setdefault(target, []).append({
                    "from": e.src,
                    "from_partition": render_key(sk),
                    "edge": e.kind,
                })
        for lst in sources.values():
            lst.sort(key=lambda d: (str(d["from"]), d["edge"], str(d["from_partition"])))
        return sources


# ----------------------------------------------------------------------
# 分区模式响应装配
# ----------------------------------------------------------------------
def _point_joined(engine: "PartitionedEngine", point) -> "Octagon | None":
    """该点全部可达槽位的凸包:与单分区模式同一点不变量语义对齐。"""
    slots = list(engine.inv[point].values())
    if not slots:
        return None
    joined = slots[0]
    for s in slots[1:]:
        joined = joined.join(s)
    return joined


def _point_incoming(engine: "PartitionedEngine", point) -> list:
    incoming = []
    if point == 0:
        incoming.append({"from": "entry", "kind": "entry"})
    for e in engine.in_edges[point]:
        incoming.append({"from": e.src, "kind": e.kind})
    incoming.sort(key=lambda d: (str(d["from"]), d["kind"]))
    return incoming


def _sorted_slots(engine: "PartitionedEngine", point) -> list:
    return sorted(engine.inv[point])


def analyze_partitioned(prog, budget: int) -> dict:
    """budget >= 2 时的审计入口:逐槽位不动点 + 全分区蕴含裁决。"""
    engine = PartitionedEngine(prog, budget)
    violations = engine.run()
    if violations:  # 理论上不发生;宁可报错也不放行
        return {"verdict": "error", "reason": "fixpoint_verification_failed",
                "violations": violations}

    sources_all = {p: engine.slot_incoming(p) for p in engine.points}

    points_view = {}
    for p in engine.points:
        joined = _point_joined(engine, p)
        slots_view = []
        for slot in _sorted_slots(engine, p):
            slots_view.append({
                "key": render_key(slot),
                "key_text": key_text(slot),
                "invariant": engine.inv[p][slot].canonical(),
                "incoming": sources_all[p].get(slot, []),
            })
        points_view[str(p)] = {
            "reachable": joined is not None,
            "invariant": joined.canonical() if joined is not None else None,
            "incoming": _point_incoming(engine, p),
            "partitions": slots_view,
        }

    assertions = []
    unproven = []  # (point, cond, [(slot, details)], joined)
    for point in sorted(prog.asserts):
        cond = prog.asserts[point]
        if not engine.inv[point]:
            assertions.append({"point": point, "condition": cond.text, "status": "unreachable"})
            continue
        slot_results = []
        failing_slots = []
        for slot in _sorted_slots(engine, point):
            ok, details = check_assertion(engine.inv[point][slot], cond)
            slot_results.append({
                "key": render_key(slot),
                "key_text": key_text(slot),
                "status": "proven" if ok else "unproven",
                "bounds": details,
            })
            if not ok:
                failing_slots.append((slot, details))
        joined = _point_joined(engine, point)
        j_ok, j_details = check_assertion(joined, cond)
        entry = {
            "point": point,
            "condition": cond.text,
            "status": "proven" if not failing_slots else "unproven",
            "bounds": j_details,  # 点级凸包上的核对,与单分区语义对齐
            "partitions": slot_results,
        }
        assertions.append(entry)
        if failing_slots:
            unproven.append((point, cond, failing_slots, joined))

    merges = sorted(
        engine.merge_log,
        key=lambda r: (str(r["point"]), r["reason"],
                       str(r.get("surviving_key")), str(r.get("edge"))),
    )
    response = {
        "verdict": "pass" if not unproven else "fail",
        "program": {"num_registers": prog.nregs, "num_instructions": prog.n_instr},
        "refinement": {
            "enabled": True,
            "budget": budget,
            "history_window": engine.window,
            "partitions_per_point": {
                str(p): len(engine.inv[p]) for p in engine.points
            },
        },
        "points": points_view,
        "assertions": assertions,
        "fixpoint": {
            "widening_points": sorted(prog.widening_points),
            "ascending_iterations": engine.ascending_iterations,
            "descending_passes": engine.descending_passes,
            "post_fixpoint_verified": True,
        },
        "partition_merges": merges,
    }
    if unproven:
        point, cond, failing_slots, joined = min(unproven, key=lambda u: u[0])
        response["first_unproven"] = {
            "point": point,
            "condition": cond.text,
            "abstract_state": joined.canonical(),
            "kind": "abstract_alarm",
            "note": "抽象解释上近似告警:存在保留分区的不变量无法蕴含该包线条件;"
                    "此处给出的是各未覆盖分区的规范抽象边界,并非具体执行反例。",
            "uncovered_partitions": [
                {
                    "key": render_key(slot),
                    "key_text": key_text(slot),
                    "abstract_state": engine.inv[point][slot].canonical(),
                    "uncovered": [d for d in details if not d["implied"]],
                }
                for slot, details in sorted(failing_slots, key=lambda t: t[0])
            ],
        }
    return response
