"""有限精化分区引擎单元测试。

覆盖:
  * 合流凸包伪状态在分支跟踪分区下被消除(安全/危险支不提前汇合);
  * 回边逐槽 widening、下降复算与逐分区转移校验;
  * 预算耗尽按固定规则合并(只合并不丢执行)及合并原因台账;
  * 断言须全部保留分区蕴含,否则按首个稳定编号点给出未覆盖分区规范边界;
  * 未选择精化 / budget=1 的响应严格兼容;非法 refinement 合并报错;
  * 下降加强破坏归纳性时回退到上一归纳后不动点。
"""
import copy
import json
import unittest

from app.analyzer import analyze


def fork_guard_program():
    """两支 x0=0 / x0=2,合流凸包含伪点 x0=1;经 x0>=1 守卫后:
    单分区只能给出 [1,2],无法证 x0==2;分区后 x0=0 支不可行,x0==2 可证。"""
    return {
        "num_registers": 2,
        "initial": [{"lo": 0, "hi": 0}, {"lo": 0, "hi": 1}],
        "instructions": [
            {"id": 0, "op": "set", "reg": 0, "value": 0},
            {"id": 1, "op": "branch",
             "cond": {"coefs": {"1": 1}, "op": "<=", "value": 0}, "target": 5},
            {"id": 2, "op": "add", "reg": 0, "value": 2},
            {"id": 3, "op": "goto", "target": 6},
            {"id": 4, "op": "add", "reg": 0, "value": 0},
            {"id": 5, "op": "add", "reg": 0, "value": 0},
            {"id": 6, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": ">=", "value": 1}, "target": 8},
            {"id": 7, "op": "halt"},
            {"id": 8, "op": "assert",
             "cond": {"coefs": {"0": 1}, "op": "==", "value": 2}},
            {"id": 9, "op": "halt"},
        ],
    }


def sync_loop_program():
    """x0、x1 同步自增循环;回边目标点 2 在 budget>=2 时保留首访/回边两槽。"""
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
    """x1 初值 0..2 三路分别置 x0=0/2/4,汇合于点 10 断言 x0<=2。"""
    return {
        "num_registers": 2,
        "initial": [{"lo": 0, "hi": 0}, {"lo": 0, "hi": 2}],
        "instructions": [
            {"id": 0, "op": "branch",
             "cond": {"coefs": {"1": 1}, "op": "<=", "value": 0}, "target": 6},
            {"id": 1, "op": "branch",
             "cond": {"coefs": {"1": 1}, "op": "<=", "value": 1}, "target": 8},
            {"id": 2, "op": "set", "reg": 0, "value": 4},
            {"id": 3, "op": "goto", "target": 10},
            {"id": 4, "op": "halt"},
            {"id": 5, "op": "halt"},
            {"id": 6, "op": "set", "reg": 0, "value": 0},
            {"id": 7, "op": "goto", "target": 10},
            {"id": 8, "op": "set", "reg": 0, "value": 2},
            {"id": 9, "op": "goto", "target": 10},
            {"id": 10, "op": "assert",
             "cond": {"coefs": {"0": 1}, "op": "<=", "value": 2}},
            {"id": 11, "op": "halt"},
        ],
    }


def with_budget(prog, budget):
    p = copy.deepcopy(prog)
    p["refinement"] = {"budget": budget}
    return p


class TestRefinementPrecision(unittest.TestCase):
    def test_fork_guard_single_partition_false_alarm(self):
        res = analyze(fork_guard_program())
        self.assertEqual(res["verdict"], "fail")
        self.assertEqual(res["first_unproven"]["point"], 8)

    def test_fork_guard_partition_proves(self):
        res = analyze(with_budget(fork_guard_program(), 2))
        self.assertEqual(res["verdict"], "pass")
        # 危险支在 x0>=1 守卫处不可行,点 8 仅保留一个槽且 x0==2
        slots = res["points"]["8"]["partitions"]
        self.assertEqual(len(slots), 1)
        texts = [c["text"] for c in slots[0]["invariant"]]
        self.assertIn("x0 <= 2", texts)
        self.assertIn("-x0 <= -2", texts)
        # 点 6 上两支互不混淆
        keys6 = {s["key_text"] for s in res["points"]["6"]["partitions"]}
        self.assertEqual(keys6, {"b1=t", "b1=f"})
        # 断言逐分区状态全部 proven
        a = next(a for a in res["assertions"] if a["point"] == 8)
        self.assertEqual({s["status"] for s in a["partitions"]}, {"proven"})

    def test_sync_loop_slotwise_widening_and_descending(self):
        res = analyze(with_budget(sync_loop_program(), 2))
        self.assertEqual(res["verdict"], "pass")
        self.assertTrue(res["fixpoint"]["post_fixpoint_verified"])
        self.assertEqual(res["fixpoint"]["widening_points"], [2])
        self.assertGreaterEqual(res["fixpoint"]["descending_passes"], 1)
        # 回边目标点 2:root 为首访(x0=0),b2=t 为回边(下降恢复 x0<=5)
        slots = {s["key_text"]: s for s in res["points"]["2"]["partitions"]}
        self.assertEqual(set(slots), {"root", "b2=t"})
        root_texts = [c["text"] for c in slots["root"]["invariant"]]
        back_texts = [c["text"] for c in slots["b2=t"]["invariant"]]
        self.assertIn("x0 <= 0", root_texts)
        self.assertIn("x0 <= 5", back_texts)
        self.assertIn("x0 - x1 <= 0", back_texts)
        # 逐槽入边来源:root 只来自顺序首访,b2=t 只来自回边
        root_src = {(d["from"], d["edge"]) for d in slots["root"]["incoming"]}
        back_src = {(d["from"], d["edge"]) for d in slots["b2=t"]["incoming"]}
        self.assertEqual(root_src, {(1, "fallthrough")})
        self.assertEqual(back_src, {(8, "goto")})

    def test_partition_incoming_carries_source_partition(self):
        res = analyze(with_budget(fork_guard_program(), 3))
        self.assertEqual(res["verdict"], "pass")
        slot = res["points"]["8"]["partitions"][0]
        # 调用方可凭 from + from_partition + edge 独立重放该槽入边
        self.assertEqual(slot["incoming"], [{
            "from": 6,
            "from_partition": [{"branch": 1, "direction": "false"}],
            "edge": "branch_true",
        }])


class TestBudgetMerge(unittest.TestCase):
    def test_budget_exhausted_merges_without_dropping(self):
        res = analyze(with_budget(three_way_program(), 2))
        # 三路但预算 2:第三路按固定规则并入最小键槽,x0=4 仍导致不可证
        self.assertEqual(res["verdict"], "fail")
        self.assertEqual(res["points"]["10"]["reachable"], True)
        self.assertEqual(len(res["points"]["10"]["partitions"]), 2)
        merge = next(m for m in res["partition_merges"]
                     if m["reason"] == "budget_exhausted_merge_into_min_key"
                     and m["point"] == 10)
        self.assertEqual(merge["surviving_key"], [{"branch": 0, "direction": "true"}])
        self.assertEqual(merge["merged_key"], [{"branch": 1, "direction": "false"}])
        self.assertEqual(merge["edge"], {"from": 3, "to": 10, "kind": "goto"})
        # 首个未证点与未覆盖分区规范边界
        first = res["first_unproven"]
        self.assertEqual(first["point"], 10)
        self.assertEqual(first["kind"], "abstract_alarm")
        self.assertIn("并非具体执行反例", first["note"])
        self.assertEqual(len(first["uncovered_partitions"]), 1)
        up = first["uncovered_partitions"][0]
        self.assertIn("x0 <= 4", [c["text"] for c in up["abstract_state"]])
        self.assertEqual(up["uncovered"][0]["bound"], 4)
        self.assertEqual(up["uncovered"][0]["required"], 2)

    def test_larger_budget_separates_all_three_ways(self):
        res = analyze(with_budget(three_way_program(), 3))
        self.assertEqual(res["verdict"], "fail")
        keys = {s["key_text"] for s in res["points"]["10"]["partitions"]}
        self.assertEqual(keys, {"b0=t", "b0=f,b1=t", "b0=f,b1=f"})
        # 预算充足则无预算合并记录
        self.assertFalse([m for m in res["partition_merges"]
                          if m["reason"] == "budget_exhausted_merge_into_min_key"])

    def test_all_partitions_must_imply(self):
        # 同一路径上两个断言点:即使点级凸包看似有界,任一槽不蕴含即 fail
        res = analyze(with_budget(three_way_program(), 3))
        a = next(a for a in res["assertions"] if a["point"] == 10)
        statuses = {s["key_text"]: s["status"] for s in a["partitions"]}
        self.assertEqual(statuses["b0=f,b1=f"], "unproven")
        self.assertEqual(statuses["b0=t"], "proven")
        self.assertEqual(statuses["b0=f,b1=t"], "proven")

    def test_window_truncation_logged_as_merge(self):
        # 循环内反复分支超过历史窗口:截断为确定性合流并记录
        res = analyze(with_budget(sync_loop_program(), 2))
        reasons = {(m["point"], m["reason"]) for m in res["partition_merges"]}
        self.assertIn((3, "history_window_truncation"), reasons)
        self.assertIn((6, "history_window_truncation"), reasons)


class TestCompatibility(unittest.TestCase):
    def test_default_and_budget_one_byte_identical(self):
        base = analyze(sync_loop_program())
        for extra in ({}, {"budget": 1}, {"budget": 1, "ignored": True}):
            p = sync_loop_program()
            p["refinement"] = extra
            other = analyze(p)
            self.assertEqual(
                json.dumps(base, sort_keys=True, ensure_ascii=False),
                json.dumps(other, sort_keys=True, ensure_ascii=False))

    def test_default_response_has_no_partition_fields(self):
        res = analyze(sync_loop_program())
        self.assertNotIn("partitions", res["points"]["2"])
        self.assertNotIn("partition_merges", res)
        self.assertNotIn("refinement", res)

    def test_invalid_refinement_merged_with_structural_errors(self):
        for bad in ({"budget": 0}, {"budget": 9}, {"budget": "2"}, {"budget": True}):
            p = sync_loop_program()
            p["refinement"] = bad
            res = analyze(p)
            self.assertEqual(res["verdict"], "error")
            self.assertEqual(res["reason"], "structural_errors")
            self.assertIn("invalid_refinement", [e["kind"] for e in res["errors"]])
            self.assertNotIn("points", res)

    def test_refinement_must_be_object(self):
        p = sync_loop_program()
        p["refinement"] = "no"
        res = analyze(p)
        self.assertEqual(res["verdict"], "error")
        self.assertIn("invalid_refinement", [e["kind"] for e in res["errors"]])


class TestDescendingRollback(unittest.TestCase):
    def test_half_strengthened_descending_rolls_back_to_inductive_fixpoint(self):
        # 回归:Gauss-Seidel 下降在轮次上限停在半加强状态时曾破坏归纳性,
        # 终态校验报错。回退后必须 verified 且结论可靠。
        prog = {
            "num_registers": 3,
            "initial": [{"lo": 1, "hi": 2}, {"lo": 1, "hi": 2}, {"lo": 0, "hi": 2}],
            "instructions": [
                {"id": 0, "op": "add", "reg": 1, "value": 0},
                {"id": 1, "op": "set", "reg": 0, "value": -2},
                {"id": 2, "op": "set", "reg": 0, "value": -2},
                {"id": 3, "op": "branch",
                 "cond": {"coefs": {"0": 1, "2": 1}, "op": ">", "value": -2}, "target": 4},
                {"id": 4, "op": "branch",
                 "cond": {"coefs": {"1": 1, "2": -1}, "op": ">", "value": 3}, "target": 4},
                {"id": 5, "op": "branch",
                 "cond": {"coefs": {"1": 1, "2": 1}, "op": ">", "value": -1}, "target": 0},
                {"id": 6, "op": "set", "reg": 1, "value": 1},
                {"id": 7, "op": "halt"},
            ],
        }
        for budget in (2, 3, 8):
            res = analyze(with_budget(prog, budget))
            self.assertNotEqual(res.get("reason"), "fixpoint_verification_failed")
            self.assertTrue(res["fixpoint"]["post_fixpoint_verified"])


if __name__ == "__main__":
    unittest.main()
