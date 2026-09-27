"""不动点分析引擎:八边形域上的上升(widening)/下降(持续复算)迭代与断言判定。

流程:
  1. 结构校验(失败则合并反馈,不产生任何分析证据);
  2. 上升迭代:混沌工作集算法,回边目标处施加固定规则 widening,保证终止;
  3. 下降复算:自后不动点出发按 Gauss-Seidel 次序反复重算各点并取交,
     逐步回收 widening 损失的精度,每一步都仍是后不动点;
  4. 终态校验:逐条转移显式复核 f(inv[p]) ⊑ inv[q],确保输出确实为
     归纳不变量,调用方可凭响应中的逐点约束与入边来源独立重放该检查;
  5. 断言判定:每个可达断言须被该点不变量蕴含,否则按程序点编号给出
     首个未证位置、进入该点的抽象边界与未被涵盖的包线条件(抽象告警,
     不伪称具体执行反例)。

精化(可选):请求携带 {"refinement": {"max_partitions": B}}(2..8)时,
每个程序点最多保留 B 个互不混淆的分区。分区随比较分支稳定产生
(令牌 = 最近 d 次分支决断,b 为分支点编号、t/f 为真假方向,d=B-1),
安全分支与危险分支不再在汇合点被凸包过早合并。各分区独立经历回边
widening、下降复算与转移校验;预算耗尽时按固定规则(并入该点字典序
最小的现存分区,凸包 join)合流,绝不丢弃任何可达执行。未选择精化或
预算为 1 时使用单状态引擎,响应结构与结论与旧版完全一致。
"""
from __future__ import annotations

from collections import deque

from .octagon import INF, Octagon, neg_terms, terms_text
from .program import EXIT, parse_program

MAX_DESCENDING_PASSES = 8
MAX_PARTITIONS = 8


def _apply_action(state: Octagon, action: tuple) -> "Octagon | None":
    """对一条出边施加迁移函数;结果为空(不可行)时返回 None。"""
    kind = action[0]
    out = state.copy()
    if kind == "set":
        out.assign_const(action[1], action[2])
    elif kind == "add":
        out.shift_const(action[1], action[2])
    elif kind == "guard":
        for terms, k in action[1]:
            out.meet(terms, k)
            if out.empty:
                return None
    return None if out.empty else out


def _guard_text(action: tuple) -> list:
    """把 guard 迁移收窄的约束渲染为规范化文本,供调用方重算转移。"""
    if action[0] != "guard":
        return []
    return [f"{terms_text(terms)} <= {k}" for terms, k in action[1]]


# ----------------------------------------------------------------------
# 精化预算解析
# ----------------------------------------------------------------------
def _is_int(x) -> bool:
    return isinstance(x, int) and not isinstance(x, bool)


def parse_refinement(payload) -> tuple:
    """解析可选精化预算。返回 (budget, errors);budget=1 表示旧版单状态分析。"""
    raw = payload.get("refinement")
    if raw is None:
        return 1, []
    if not isinstance(raw, dict):
        return 1, [{"kind": "invalid_refinement_budget",
                    "detail": "'refinement' must be an object"}]
    budget = raw.get("max_partitions", 1)
    if not _is_int(budget) or not (1 <= budget <= MAX_PARTITIONS):
        return 1, [{"kind": "invalid_refinement_budget",
                    "detail": f"'max_partitions' must be an integer within 1..{MAX_PARTITIONS}",
                    "value": budget}]
    return budget, []


# ======================================================================
# 引擎一(默认 / 预算 1):每点单个八边形状态
# ======================================================================
class _Engine:
    def __init__(self, prog):
        self.prog = prog
        self.points = prog.points
        self.inv = {p: None for p in self.points}  # None 表示 ⊥(不可达)
        self.in_edges = {p: [] for p in self.points}
        self.out_edges = {p: [] for p in self.points}
        for e in prog.edges:
            self.out_edges[e.src].append(e)
            self.in_edges[e.dst].append(e)
        self.initial = self._initial_state()
        self.ascending_iterations = 0
        self.descending_passes = 0

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
    # 上升:widening 作用于回边目标,保证稳定
    # ------------------------------------------------------------------
    def _ascending(self) -> None:
        inv = self.inv
        inv[0] = self.initial
        work = deque([0])
        in_work = {0}
        widen_at = self.prog.widening_points
        while work:
            p = work.popleft()
            in_work.discard(p)
            src = inv[p]
            if src is None:
                continue
            for e in self.out_edges[p]:
                y = _apply_action(src, e.action)
                if y is None:
                    continue
                q = e.dst
                old = inv[q]
                if old is None:
                    inv[q] = y
                else:
                    joined = old.join(y)
                    if joined.incl(old):
                        continue
                    inv[q] = old.widen(joined) if q in widen_at else joined
                if q not in in_work:
                    work.append(q)
                    in_work.add(q)
                self.ascending_iterations += 1

    # ------------------------------------------------------------------
    # 下降:widening 之后持续复算不变量,逐步回收精度
    # ------------------------------------------------------------------
    def _descending(self) -> None:
        inv = self.inv
        for _ in range(MAX_DESCENDING_PASSES):
            changed = False
            for q in self.points:
                cur = inv[q]
                if cur is None:
                    continue  # 不可达点保持 ⊥
                contrib = self.initial.copy() if q == 0 else None
                for e in self.in_edges[q]:
                    s = inv[e.src]
                    if s is None:
                        continue
                    y = _apply_action(s, e.action)
                    if y is None:
                        continue
                    contrib = y if contrib is None else contrib.join(y)
                if contrib is None:
                    continue
                new = contrib.meet_with(cur)
                if new.empty:
                    inv[q] = None
                    changed = True
                    continue
                if new.incl(cur) and cur.incl(new):
                    continue
                inv[q] = new
                changed = True
            self.descending_passes += 1
            if not changed:
                break

    # ------------------------------------------------------------------
    # 终态校验:逐条转移显式复核不变量保持性
    # ------------------------------------------------------------------
    def _verify(self) -> list:
        violations = []
        head = self.inv[0]
        if head is None or not self.initial.incl(head):
            violations.append({"from": "entry", "to": 0, "kind": "entry"})
        for p in self.points:
            src = self.inv[p]
            if src is None:
                continue
            for e in self.out_edges[p]:
                y = _apply_action(src, e.action)
                if y is None:
                    continue
                dst = self.inv[e.dst]
                if dst is None or not y.incl(dst):
                    violations.append({"from": p, "to": e.dst, "kind": e.kind})
        return violations

    def run(self) -> list:
        self._ascending()
        self._descending()
        return self._verify()


# ======================================================================
# 引擎二(精化预算 B>=2):有界轨迹分区,各分区独立不动点
# ======================================================================
def _render_token(token: tuple) -> str:
    """令牌的稳定文本标识,如 'b2:t|b5:f';空令牌为 'root'。"""
    if not token:
        return "root"
    return "|".join(f"b{bid}:{'t' if sense else 'f'}" for bid, sense in token)


class _PartitionEngine:
    """每点维护 token -> Octagon 的至多 B 个分区(值为 None 表示 ⊥)。"""

    def __init__(self, prog, budget: int):
        self.prog = prog
        self.budget = budget
        self.history_depth = max(1, budget - 1)
        self.points = prog.points
        self.in_edges = {p: [] for p in self.points}
        self.out_edges = {p: [] for p in self.points}
        for e in prog.edges:
            self.out_edges[e.src].append(e)
            self.in_edges[e.dst].append(e)
        # inv[p]: {token: Octagon | None}
        self.inv = {p: {} for p in self.points}
        # meta[p]: {token: {origin, incoming(set), merges(list), widened(bool)}}
        self.meta = {p: {} for p in self.points}
        # 预算耗尽被吸收的令牌:(point, token) -> 实际并入的目标令牌
        self.absorbed = {}
        self.initial = self._initial_state()
        self.ascending_iterations = 0
        self.descending_passes = 0

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
    # 分区令牌:仅比较分支产生/截断决断,其余边原样携带
    # ------------------------------------------------------------------
    def _step_token(self, token: tuple, edge) -> tuple:
        if edge.kind == "branch_true":
            return (token + ((edge.src, True),))[-self.history_depth:]
        if edge.kind == "branch_false":
            return (token + ((edge.src, False),))[-self.history_depth:]
        return token

    def _route(self, q, token: tuple) -> tuple:
        """下降/校验阶段复用上升阶段的固定合流规则。"""
        if token in self.inv[q]:
            return token
        return self.absorbed[(q, token)]

    # ------------------------------------------------------------------
    # 上升:逐分区工作集,回边目标处对各分区分别 widening
    # ------------------------------------------------------------------
    def _ascending(self) -> None:
        inv, meta = self.inv, self.meta
        inv[0][()] = self.initial
        meta[0][()] = {
            "origin": {"from": "entry", "partition": None, "edge": "entry",
                       "decision": None, "guards": []},
            "incoming": set(),
            "merges": [],
            "widened": False,
        }
        work = deque([(0, ())])
        in_work = {(0, ())}
        widen_at = self.prog.widening_points
        while work:
            p, token = work.popleft()
            in_work.discard((p, token))
            src = inv[p].get(token)
            if src is None:
                continue
            for e in self.out_edges[p]:
                y = _apply_action(src, e.action)
                if y is None:
                    continue
                q = e.dst
                new_token = self._step_token(token, e)
                target = new_token
                slots, qmeta = inv[q], meta[q]
                incoming_key = (p, _render_token(token), e.kind)
                if target in slots:
                    qmeta[target]["incoming"].add(incoming_key)
                    old = slots[target]
                    if old is None:
                        slots[target] = y
                        grew = True
                    else:
                        joined = old.join(y)
                        grew = not joined.incl(old)
                        if grew:
                            if q in widen_at:
                                slots[target] = old.widen(joined)
                                qmeta[target]["widened"] = True
                            else:
                                slots[target] = joined
                elif len(slots) < self.budget:
                    # 预算内:随比较分支稳定产生新分区
                    slots[target] = y
                    qmeta[target] = {
                        "origin": {"from": p, "partition": _render_token(token),
                                   "edge": e.kind,
                                   "decision": (f"b{e.src}:true" if e.kind == "branch_true"
                                                else f"b{e.src}:false" if e.kind == "branch_false"
                                                else None),
                                   "guards": _guard_text(e.action)},
                        "incoming": {incoming_key},
                        "merges": [],
                        "widened": False,
                    }
                    grew = True
                else:
                    # 预算耗尽:固定规则合入字典序最小的现存分区(凸包 join,
                    # 仅放宽上近似,不丢弃任何可达执行)
                    target = min(slots)
                    self.absorbed.setdefault((q, new_token), target)
                    qmeta[target]["incoming"].add(incoming_key)
                    record = {
                        "reason": "budget_exhausted",
                        "absorbed_partition": _render_token(new_token),
                        "edge": {"from": p, "from_partition": _render_token(token),
                                "kind": e.kind, "guards": _guard_text(e.action)},
                    }
                    if record not in qmeta[target]["merges"]:
                        qmeta[target]["merges"].append(record)
                    old = slots[target]
                    joined = y if old is None else old.join(y)
                    grew = old is None or not joined.incl(old)
                    if grew:
                        if q in widen_at:
                            slots[target] = old.widen(joined) if old is not None else joined
                            qmeta[target]["widened"] = True
                        else:
                            slots[target] = joined
                if grew and (q, target) not in in_work:
                    work.append((q, target))
                    in_work.add((q, target))
                    self.ascending_iterations += 1

    # ------------------------------------------------------------------
    # 下降:逐分区复算,合流规则与上升完全一致
    # ------------------------------------------------------------------
    def _descending(self) -> None:
        inv = self.inv
        for _ in range(MAX_DESCENDING_PASSES):
            changed = False
            for q in self.points:
                if not inv[q]:
                    continue
                contrib = {}
                if q == 0:
                    contrib[()] = self.initial.copy()
                for e in self.in_edges[q]:
                    for srctok, s in inv[e.src].items():
                        if s is None:
                            continue
                        y = _apply_action(s, e.action)
                        if y is None:
                            continue
                        target = self._route(q, self._step_token(srctok, e))
                        acc = contrib.get(target)
                        contrib[target] = y if acc is None else acc.join(y)
                for token, cur in list(inv[q].items()):
                    c = contrib.get(token)
                    if c is None or cur is None:
                        continue
                    new = c.meet_with(cur)
                    if new.empty:
                        inv[q][token] = None
                        changed = True
                        continue
                    if new.incl(cur) and cur.incl(new):
                        continue
                    inv[q][token] = new
                    changed = True
            self.descending_passes += 1
            if not changed:
                break

    # ------------------------------------------------------------------
    # 终态校验:对每个保留分区逐条转移显式复核
    # ------------------------------------------------------------------
    def _verify(self) -> list:
        violations = []
        head = self.inv[0].get(())
        if head is None or not self.initial.incl(head):
            violations.append({"from": "entry", "to": 0, "kind": "entry",
                               "partition": "root"})
        for p in self.points:
            for token, src in self.inv[p].items():
                if src is None:
                    continue
                for e in self.out_edges[p]:
                    y = _apply_action(src, e.action)
                    if y is None:
                        continue
                    target = self._route(e.dst, self._step_token(token, e))
                    dst = self.inv[e.dst].get(target)
                    if dst is None or not y.incl(dst):
                        violations.append({"from": p, "to": e.dst, "kind": e.kind,
                                           "partition": _render_token(token)})
        return violations

    def run(self) -> list:
        self._ascending()
        self._descending()
        return self._verify()


# ----------------------------------------------------------------------
# 断言蕴含判定
# ----------------------------------------------------------------------
def _bound_detail(state: Octagon, terms: tuple, k: int, disjunction: bool = False) -> dict:
    b = state.bound(terms) if terms else 0
    detail = {
        "text": f"{terms_text(terms)} <= {k}",
        "bound": None if b == INF else b,
        "required": k,
        "implied": b <= k,
    }
    if disjunction:
        detail["disjunction"] = True
    return detail


def _check_assertion(state: Octagon, cond) -> tuple:
    """返回 (是否被蕴含, 逐条件界信息)。!= 以两个析取支检查。"""
    terms, kind, k = cond.terms, cond.kind, cond.k
    if kind == "le":
        details = [_bound_detail(state, terms, k)]
        return details[0]["implied"], details
    if kind == "eq":
        details = [
            _bound_detail(state, terms, k),
            _bound_detail(state, neg_terms(terms), -k),
        ]
        return all(d["implied"] for d in details), details
    # ne:expr <= k-1 或 -expr <= -k-1 任一成立即蕴含
    details = [
        _bound_detail(state, terms, k - 1, disjunction=True),
        _bound_detail(state, neg_terms(terms), -k - 1, disjunction=True),
    ]
    return any(d["implied"] for d in details), details


# ----------------------------------------------------------------------
# 输出装配
# ----------------------------------------------------------------------
def _join_all(states: list) -> "Octagon | None":
    out = None
    for s in states:
        if s is None:
            continue
        out = s.copy() if out is None else out.join(s)
    return out


def _incoming_view(engine: _Engine, p) -> list:
    incoming = []
    if p == 0:
        incoming.append({"from": "entry", "kind": "entry"})
    for e in engine.in_edges[p]:
        incoming.append({"from": e.src, "kind": e.kind})
    incoming.sort(key=lambda d: (str(d["from"]), d["kind"]))
    return incoming


def _points_view(engine) -> dict:
    out = {}
    for p in engine.points:
        state = engine.inv[p]
        out[str(p)] = {
            "reachable": state is not None,
            "invariant": state.canonical() if state is not None else None,
            "incoming": _incoming_view(engine, p),
        }
    return out


def _partition_view(engine: _PartitionEngine) -> dict:
    out = {}
    for p in engine.points:
        slots = engine.inv[p]
        parts = []
        for token in sorted(slots):
            state = slots[token]
            m = engine.meta[p][token]
            parts.append({
                "id": _render_token(token),
                "reachable": state is not None,
                # 强闭包后的规范化约束(闭包约束),调用方可独立重算入边与转移
                "closure_constraints": state.canonical() if state is not None else None,
                "origin": m["origin"],
                "incoming": sorted(
                    ({"from": s, "partition": tk, "edge": kind}
                     for s, tk, kind in m["incoming"]),
                    key=lambda d: (str(d["from"]), d["partition"], d["edge"])),
                "merges": m["merges"],
                "widening_applied": m["widened"],
            })
        joined = _join_all([s for s in slots.values() if s is not None])
        out[str(p)] = {
            "reachable": joined is not None,
            "invariant": joined.canonical() if joined is not None else None,
            "incoming": _incoming_view(engine, p),
            "partitions": parts,
        }
    return out


def _widened_partitions(engine: _PartitionEngine) -> list:
    out = []
    for p in engine.points:
        for token in sorted(engine.inv[p]):
            if engine.meta[p][token]["widened"]:
                out.append({"point": p, "partition": _render_token(token)})
    return out


def _assertion_records_legacy(engine: _Engine, prog) -> tuple:
    """返回 (assertions 响应列表, 未证 (point, cond, payload-ish) 列表)。"""
    assertions, unproven = [], []
    for point in sorted(prog.asserts):
        cond = prog.asserts[point]
        state = engine.inv[point]
        if state is None:
            assertions.append({"point": point, "condition": cond.text,
                               "status": "unreachable"})
            continue
        ok, details = _check_assertion(state, cond)
        assertions.append({"point": point, "condition": cond.text,
                           "status": "proven" if ok else "unproven", "bounds": details})
        if not ok:
            unproven.append((point, cond, state, details, None, None))
    return assertions, unproven


def _assertion_records_partitioned(engine: _PartitionEngine, prog) -> tuple:
    assertions, unproven = [], []
    for point in sorted(prog.asserts):
        cond = prog.asserts[point]
        slots = engine.inv[point]
        live = [(t, s) for t, s in slots.items() if s is not None]
        if not live:
            assertions.append({"point": point, "condition": cond.text,
                               "status": "unreachable"})
            continue
        part_records, failing = [], []
        for token, state in sorted(live):
            ok, details = _check_assertion(state, cond)
            pid = _render_token(token)
            part_records.append({"partition": pid,
                                 "status": "proven" if ok else "unproven",
                                 "bounds": details})
            if not ok:
                failing.append((token, state, details))
        ok_all = not failing
        assertions.append({"point": point, "condition": cond.text,
                           "status": "proven" if ok_all else "unproven",
                           "partitions": part_records})
        if failing:
            # 同点内取稳定标识最小的未证分区
            token, state, details = min(failing, key=lambda f: _render_token(f[0]))
            unproven.append((point, cond, state, details, part_records,
                             _render_token(token)))
    return assertions, unproven


def analyze(payload) -> dict:
    """审计入口:返回 pass / fail / error 三种结论之一。"""
    prog, errors = parse_program(payload)
    budget, refine_errors = parse_refinement(payload)
    errors = errors + refine_errors
    if errors:
        # 结构问题合并反馈;不附带任何(旧)分析证据
        return {"verdict": "error", "reason": "structural_errors", "errors": errors}

    if budget == 1:
        engine = _Engine(prog)
        violations = engine.run()
        if violations:  # 理论上不发生;宁可报错也不放行
            return {"verdict": "error", "reason": "fixpoint_verification_failed",
                    "violations": violations}
        assertions, unproven = _assertion_records_legacy(engine, prog)
        points_view = _points_view(engine)
        fixpoint = {
            "widening_points": sorted(prog.widening_points),
            "ascending_iterations": engine.ascending_iterations,
            "descending_passes": engine.descending_passes,
            "post_fixpoint_verified": True,
        }
    else:
        engine = _PartitionEngine(prog, budget)
        violations = engine.run()
        if violations:
            return {"verdict": "error", "reason": "fixpoint_verification_failed",
                    "violations": violations}
        assertions, unproven = _assertion_records_partitioned(engine, prog)
        points_view = _partition_view(engine)
        fixpoint = {
            "refinement": {
                "active": True,
                "max_partitions": budget,
                "history_depth": engine.history_depth,
                "merge_rule": "on_budget_exhausted_join_into_lexicographically_smallest_partition",
            },
            "widening_points": sorted(prog.widening_points),
            "widened_partitions": _widened_partitions(engine),
            "ascending_iterations": engine.ascending_iterations,
            "descending_passes": engine.descending_passes,
            "post_fixpoint_verified": True,
        }

    response = {
        "verdict": "pass" if not unproven else "fail",
        "program": {"num_registers": prog.nregs, "num_instructions": prog.n_instr},
        "points": points_view,
        "assertions": assertions,
        "fixpoint": fixpoint,
    }
    if unproven:
        point, cond, state, details, part_records, part_id = \
            min(unproven, key=lambda u: u[0])
        first = {
            "point": point,
            "condition": cond.text,
            "abstract_state": state.canonical(),
            "uncovered": [d for d in details if not d["implied"]],
            "kind": "abstract_alarm",
            "note": "抽象解释上近似告警:不变量无法蕴含该包线条件;"
                    "此处给出的是抽象边界信息,并非具体执行反例。",
        }
        if part_records is not None:
            # 精化模式:注明未覆盖分区,并列出该点全部保留分区的裁决
            first["partition"] = part_id
            first["partition_results"] = part_records
        response["first_unproven"] = first
    return response
