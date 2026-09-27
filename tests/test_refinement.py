"""精化预算(有界轨迹分区)单元测试:可选精化、预算耗尽合流、兼容旧语义。"""
import unittest

from app.analyzer import analyze


def two_branch_program(envelope):
    """安全分支(x0<=0 方向)与危险分支(否则 x0:=10)在断言点汇合。"""
    return {
        "num_registers": 1,
        "initial": [{"lo": 0, "hi": 10}],
        "instructions": [
            {"id": 0, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": "<=", "value": 0}, "target": 2},
            {"id": 1, "op": "set", "reg": 0, "value": 10},
            {"id": 2, "op": "assert", "cond": envelope},
            {"id": 3, "op": "halt"},
        ],
    }


def loop_program():
    """x0 与 x1 同步自增的循环(与 test_analyzer 相同的放行用例)。"""
    return {
        "num_registers": 2,
        "initial": [{"lo": 0, "hi": 0}, {"lo": 0, "hi": 0}],
        "instructions": [
            {"id": 0, "op": "set", "reg": 0, "value": 0},
            {"id": 1, "op": "set", "reg": 1, "value": 0},
            {"id": 2, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": "<", "value": 5}, "target": 6},
            {"id": 3, "op": "assert",
             "cond": {"coefs": {"0": 1, "1": -1}, "op": "==", "value": 0}},
            {"id": 4, "op": "assert",
             "cond": {"coefs": {"0": 1}, "op": "<=", "value": 5}},
            {"id": 5, "op": "halt"},
            {"id": 6, "op": "add", "reg": 0, "value": 1},
            {"id": 7, "op": "add", "reg": 1, "value": 1},
            {"id": 8, "op": "goto", "target": 2},
        ],
    }


def three_way_program():
    """三个比较分支汇聚同一程序点,用于触发预算耗尽。"""
    return {
        "num_registers": 1,
        "initial": [{"lo": 0, "hi": 10}],
        "instructions": [
            {"id": 0, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": "<=", "value": 0}, "target": 6},
            {"id": 1, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": ">=", "value": 10}, "target": 6},
            {"id": 2, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": ">=", "value": 5}, "target": 6},
            {"id": 3, "op": "assert",
             "cond": {"coefs": {"0": 1}, "op": "<=", "value": 3}},
            {"id": 4, "op": "halt"},
            {"id": 5, "op": "halt"},
            {"id": 6, "op": "assert",
             "cond": {"coefs": {"0": 1}, "op": "<=", "value": 10}},
            {"id": 7, "op": "halt"},
        ],
    }


class TestPartitionPrecision(unittest.TestCase):
    def test_partition_proves_what_convex_hull_cannot(self):
        # 包线 x0 != 5 非凸:凸包 [0,10] 必然误报,两个分区各自可证
        prog = two_branch_program({"coefs": {"0": 1}, "op": "!=", "value": 5})
        legacy = analyze(prog)
        self.assertEqual(legacy["verdict"], "fail")
        self.assertEqual(legacy["first_unproven"]["point"], 2)

        refined = analyze(dict(prog, refinement={"max_partitions": 2}))
        self.assertEqual(refined["verdict"], "pass")
        entry = refined["assertions"][0]
        self.assertEqual(entry["status"], "proven")
        # 每个保留分区分别给出裁决与逐项界
        by_part = {p["partition"]: p for p in entry["partitions"]}
        self.assertEqual(set(by_part), {"b0:t", "b0:f"})
        self.assertTrue(all(p["status"] == "proven" for p in by_part.values()))

    def test_partition_provenance_and_closure_listed(self):
        prog = two_branch_program({"coefs": {"0": 1}, "op": "<=", "value": 10})
        res = analyze(dict(prog, refinement={"max_partitions": 2}))
        parts = {p["id"]: p for p in res["points"]["2"]["partitions"]}
        self.assertEqual(set(parts), {"b0:t", "b0:f"})
        # 分区来源:随比较分支稳定产生,记录来源点、来源分区与分支决断
        self.assertEqual(parts["b0:t"]["origin"]["edge"], "branch_true")
        self.assertEqual(parts["b0:t"]["origin"]["decision"], "b0:true")
        self.assertEqual(parts["b0:t"]["origin"]["from"], 0)
        self.assertEqual(parts["b0:t"]["origin"]["partition"], "root")
        # 闭包约束:强闭包后的规范化约束,调用方可独立重算入边与转移
        texts_t = [c["text"] for c in parts["b0:t"]["closure_constraints"]]
        self.assertIn("x0 <= 0", texts_t)
        texts_f = [c["text"] for c in parts["b0:f"]["closure_constraints"]]
        self.assertIn("x0 <= 10", texts_f)
        self.assertIn("-x0 <= -10", texts_f)
        # 真方向的守卫收窄项随来源给出,便于重算转移
        self.assertEqual(parts["b0:t"]["origin"]["guards"], ["x0 <= 0"])
        # 入边来源逐分区列出
        incoming = {(e["from"], e["edge"]) for e in parts["b0:f"]["incoming"]}
        self.assertIn((1, "fallthrough"), incoming)
        # 逐点汇合视图仍在(与旧版同键),且为各分区的凸包
        joined = [c["text"] for c in res["points"]["2"]["invariant"]]
        self.assertIn("x0 <= 10", joined)

    def test_refinement_echo_in_fixpoint(self):
        prog = two_branch_program({"coefs": {"0": 1}, "op": "<=", "value": 10})
        res = analyze(dict(prog, refinement={"max_partitions": 2}))
        ref = res["fixpoint"]["refinement"]
        self.assertTrue(ref["active"])
        self.assertEqual(ref["max_partitions"], 2)
        self.assertEqual(ref["history_depth"], 1)
        self.assertIn("merge_rule", ref)
        self.assertTrue(res["fixpoint"]["post_fixpoint_verified"])


class TestBudgetExhaustion(unittest.TestCase):
    def test_fixed_merge_rule_and_no_dropped_executions(self):
        res = analyze(dict(three_way_program(), refinement={"max_partitions": 2}))
        parts = res["points"]["6"]["partitions"]
        # 预算 2:只保留两个分区,第三个按固定规则并入字典序最小者
        self.assertEqual([p["id"] for p in parts], ["b0:t", "b1:t"])
        merged = parts[0]
        self.assertTrue(merged["merges"])
        merge = merged["merges"][0]
        self.assertEqual(merge["reason"], "budget_exhausted")
        self.assertEqual(merge["absorbed_partition"], "b2:t")
        self.assertEqual(merge["edge"]["from"], 2)
        # 合流为凸包 join:并入后分区覆盖被吸收的可达执行(0..9 与 5..9)
        texts = [c["text"] for c in merged["closure_constraints"]]
        self.assertIn("x0 <= 9", texts)
        self.assertIn("-x0 <= 0", texts)
        # 汇合视图覆盖全部三条路径的可达执行 [0,10],未丢弃任何执行
        joined = [c["text"] for c in res["points"]["6"]["invariant"]]
        self.assertIn("x0 <= 10", joined)
        self.assertIn("-x0 <= 0", joined)
        # 汇合点断言 x0 <= 10 在全部保留分区上成立 → 该点放行
        statuses = {a["point"]: a["status"] for a in res["assertions"]}
        self.assertEqual(statuses[6], "proven")

    def test_mid_path_assertion_still_fails_genuinely(self):
        # b2 假方向 x0 ∈ [1,4] 真实包含 x0=4,超出包线 <=3 → 精化不放行
        res = analyze(dict(three_way_program(), refinement={"max_partitions": 2}))
        self.assertEqual(res["verdict"], "fail")
        first = res["first_unproven"]
        self.assertEqual(first["point"], 3)
        self.assertEqual(first["kind"], "abstract_alarm")
        self.assertEqual(first["partition"], "b2:f")
        self.assertEqual(first["uncovered"][0]["bound"], 4)
        self.assertEqual(first["uncovered"][0]["required"], 3)


class TestPartitionedFixpoint(unittest.TestCase):
    def test_partitions_widen_and_descend_independently(self):
        res = analyze(dict(loop_program(), refinement={"max_partitions": 3}))
        self.assertEqual(res["verdict"], "pass")
        # 回边 widening 施加于分区而非汇合状态
        widened = res["fixpoint"]["widened_partitions"]
        self.assertTrue(any(w["point"] == 2 for w in widened))
        # widening 后确有下降复算
        self.assertGreaterEqual(res["fixpoint"]["descending_passes"], 1)
        # 出循环点的保留分区精确回收 x0 == x1 == 5
        parts = res["points"]["3"]["partitions"]
        self.assertTrue(parts)
        texts = [c["text"] for p in parts for c in p["closure_constraints"]]
        self.assertIn("x0 <= 5", texts)
        self.assertIn("-x0 <= -5", texts)
        self.assertIn("x0 - x1 <= 0", texts)
        self.assertIn("-x0 + x1 <= 0", texts)

    def test_loop_terminates_with_minimal_budget(self):
        # 预算 2 时循环令牌截断后合流,迭代仍终止且结论可靠
        res = analyze(dict(loop_program(), refinement={"max_partitions": 2}))
        self.assertEqual(res["verdict"], "pass")


class TestPartitionedAlarms(unittest.TestCase):
    def test_genuine_danger_identifies_uncovered_partition(self):
        # 危险分支真实违例:精化不得放行,须给出首个未证点与未覆盖分区
        prog = two_branch_program({"coefs": {"0": 1}, "op": "<=", "value": 4})
        res = analyze(dict(prog, refinement={"max_partitions": 2}))
        self.assertEqual(res["verdict"], "fail")
        first = res["first_unproven"]
        self.assertEqual(first["point"], 2)
        self.assertEqual(first["kind"], "abstract_alarm")
        self.assertIn("并非具体执行反例", first["note"])
        # 未覆盖分区为危险分支 b0:f,其规范边界 x0 <= 10 超出包线 4
        self.assertEqual(first["partition"], "b0:f")
        self.assertEqual(first["uncovered"][0]["bound"], 10)
        self.assertEqual(first["uncovered"][0]["required"], 4)
        texts = [c["text"] for c in first["abstract_state"]]
        self.assertIn("x0 <= 10", texts)
        # 全部保留分区的裁决一并列出:安全分支可证,危险分支不可证
        statuses = {p["partition"]: p["status"] for p in first["partition_results"]}
        self.assertEqual(statuses, {"b0:t": "proven", "b0:f": "unproven"})

    def test_unreachable_assertion_still_vacuous(self):
        prog = {
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "branch",
                 "cond": {"coefs": {"0": 1}, "op": ">=", "value": 1}, "target": 2},
                {"id": 1, "op": "halt"},
                {"id": 2, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": -1}},
                {"id": 3, "op": "halt"},
            ],
        }
        res = analyze(dict(prog, refinement={"max_partitions": 2}))
        self.assertEqual(res["verdict"], "pass")
        self.assertEqual(res["assertions"][0]["status"], "unreachable")


class TestRefinementCompatibility(unittest.TestCase):
    def test_invalid_budget_is_structural_error(self):
        prog = two_branch_program({"coefs": {"0": 1}, "op": "<=", "value": 10})
        for bad in (0, 9, -1, 1.5, "2", True, None):
            res = analyze(dict(prog, refinement={"max_partitions": bad}))
            self.assertEqual(res["verdict"], "error", f"budget={bad!r}")
            self.assertIn("invalid_refinement_budget",
                          {e["kind"] for e in res["errors"]})
            # 合并反馈不附带任何分析证据
            self.assertNotIn("points", res)
            self.assertNotIn("assertions", res)
        res = analyze(dict(prog, refinement="yes"))
        self.assertEqual(res["verdict"], "error")
        self.assertIn("invalid_refinement_budget",
                      {e["kind"] for e in res["errors"]})

    def test_budget_one_matches_legacy_exactly(self):
        for prog in (two_branch_program({"coefs": {"0": 1}, "op": "<=", "value": 4}),
                     loop_program(), three_way_program()):
            legacy = analyze(prog)
            for refinement in ({"max_partitions": 1}, {}):
                refined = analyze(dict(prog, refinement=refinement))
                self.assertEqual(refined, legacy,
                                 f"refinement={refinement} must be legacy-identical")

    def test_absent_refinement_has_no_partition_keys(self):
        res = analyze(two_branch_program({"coefs": {"0": 1}, "op": "<=", "value": 10}))
        self.assertNotIn("refinement", res["fixpoint"])
        self.assertNotIn("partitions", res["points"]["2"])
        self.assertNotIn("partitions", res["assertions"][0])


if __name__ == "__main__":
    unittest.main()
