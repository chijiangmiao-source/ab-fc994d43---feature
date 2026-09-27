#!/usr/bin/env python3
"""verify 容器的 HTTP 冒烟:健康路径、审计接口三类结论、镜像构建(版本)核对。

通过环境变量配置:
    APP_URL          被测服务地址(默认 http://127.0.0.1:8080)
    EXPECTED_VERSION 期望的构建版本(默认 1.0.0),与 /health 返回比对

全部检查通过以状态码 0 退出,否则状态码 1。
"""
import json
import os
import sys
import time
import urllib.error
import urllib.request

APP_URL = os.environ.get("APP_URL", "http://127.0.0.1:8080").rstrip("/")
EXPECTED_VERSION = os.environ.get("EXPECTED_VERSION", "1.0.0")
WAIT_SECONDS = float(os.environ.get("SMOKE_WAIT_SECONDS", "30"))

# 含循环与寄存器间关系的脚本: widening + 下降复算后应放行
PASS_CASE = {
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

# 不可证断言:应返回 fail,首个未证位置为程序点 2
FAIL_CASE = {
    "num_registers": 1,
    "initial": [{"lo": 0, "hi": 0}],
    "instructions": [
        {"id": 0, "op": "set", "reg": 0, "value": 0},
        {"id": 1, "op": "add", "reg": 0, "value": 5},
        {"id": 2, "op": "assert",
         "cond": {"coefs": {"0": 1}, "op": "<=", "value": 3}},
        {"id": 3, "op": "halt"},
    ],
}

# 合流凸包引入伪状态:两支 x0=0 / x0=2 汇合为 [0,2](含伪点 1),经 x0>=1
# 守卫后单分区只能给出 [1,2],无法证 x0==2;budget=2 跟踪分支后 x0=0 支在
# 守卫处不可行,仅剩 x0=2 支,应放行。
REFINEMENT_CASE = {
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

# 四类结构错误:寄存器越界 + 跳转悬空 + 不可解析约束 + 无可达终止,应合并反馈
ERROR_CASE = {
    "num_registers": 2,
    "initial": [{"lo": 0, "hi": 0}, {"lo": 0, "hi": 0}],
    "instructions": [
        {"id": 0, "op": "set", "reg": 5, "value": 1},
        {"id": 1, "op": "goto", "target": 9},
        {"id": 2, "op": "assert",
         "cond": {"coefs": {"0": 2}, "op": "<=", "value": 1}},
        {"id": 3, "op": "goto", "target": 2},
    ],
}

_failures = []


def check(name, ok, detail=""):
    mark = "PASS" if ok else "FAIL"
    print(f"[{mark}] {name}" + (f" -- {detail}" if detail and not ok else ""))
    if not ok:
        _failures.append(name)


def request(method, path, payload=None):
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    req = urllib.request.Request(APP_URL + path, data=data, method=method,
                                 headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=5) as resp:
            return resp.status, json.loads(resp.read())
    except urllib.error.HTTPError as e:
        return e.code, json.loads(e.read())


def wait_ready():
    deadline = time.time() + WAIT_SECONDS
    while time.time() < deadline:
        try:
            code, body = request("GET", "/health")
            if code == 200 and body.get("status") == "ok":
                return body
        except (OSError, ValueError):
            pass
        time.sleep(0.5)
    return None


def main():
    health = wait_ready()
    check("health endpoint reachable", health is not None)
    if health is None:
        return 1

    # 镜像构建核对:运行中的镜像须报告期望的构建版本
    check("image build version matches",
          health.get("version") == EXPECTED_VERSION,
          f"expected {EXPECTED_VERSION}, got {health.get('version')!r}")

    code, body = request("POST", "/audit", PASS_CASE)
    check("pass case verdict", code == 200 and body.get("verdict") == "pass",
          f"code={code} body={body}")
    check("pass case post-fixpoint verified",
          body.get("fixpoint", {}).get("post_fixpoint_verified") is True)
    check("pass case per-point invariants present",
          "2" in body.get("points", {}) and
          any(c["text"] == "x0 - x1 <= 0" for c in body["points"]["3"]["invariant"]))

    code, body = request("POST", "/audit", FAIL_CASE)
    first = body.get("first_unproven", {})
    check("fail case verdict", code == 200 and body.get("verdict") == "fail",
          f"code={code} body={body}")
    check("fail case first unproven point", first.get("point") == 2)
    check("fail case is abstract alarm, not counterexample",
          first.get("kind") == "abstract_alarm")
    check("fail case uncovered envelope bound",
          bool(first.get("uncovered")) and first["uncovered"][0].get("bound") == 5)

    code, body = request("POST", "/audit", ERROR_CASE)
    kinds = {e.get("kind") for e in body.get("errors", [])}
    check("error case verdict", code == 200 and body.get("verdict") == "error",
          f"code={code} body={body}")
    check("error case merges all four structural kinds",
          {"register_out_of_bounds", "dangling_jump",
           "unparseable_constraint", "no_reachable_halt"} <= kinds,
          f"kinds={kinds}")
    check("error case returns no stale evidence",
          "points" not in body and "assertions" not in body)

    # 有限精化:同一脚本未选精化时为抽象告警,budget=2 分区后放行
    code, plain = request("POST", "/audit", REFINEMENT_CASE)
    check("refinement case is alarm without partition tracking",
          code == 200 and plain.get("verdict") == "fail"
          and plain.get("first_unproven", {}).get("point") == 8,
          f"code={code} verdict={plain.get('verdict')}")
    check("unrefined response stays compatible (no partition fields)",
          "partitions" not in plain.get("points", {}).get("8", {})
          and "partition_merges" not in plain)

    refined = dict(REFINEMENT_CASE, refinement={"budget": 2})
    code, body = request("POST", "/audit", refined)
    check("refinement budget=2 verdict flips to pass",
          code == 200 and body.get("verdict") == "pass",
          f"code={code} body={body}")
    check("refinement metadata echoed",
          body.get("refinement", {}).get("budget") == 2
          and body.get("refinement", {}).get("history_window") == 1)
    p8 = body.get("points", {}).get("8", {})
    parts = p8.get("partitions", [])
    check("refinement lists surviving partition with closure",
          len(parts) == 1 and any(
              c.get("text") == "x0 <= 2" for c in parts[0].get("invariant", []))
          and any(c.get("text") == "-x0 <= -2" for c in parts[0].get("invariant", [])),
          f"partitions={parts}")
    check("partition incoming is replayable (from, from_partition, edge)",
          parts and parts[0].get("incoming") == [{
              "from": 6, "edge": "branch_true",
              "from_partition": [{"branch": 1, "direction": "false"}]}],
          f"incoming={parts[0].get('incoming') if parts else None}")
    check("partition merge reasons present",
          isinstance(body.get("partition_merges"), list))
    # 每分区转移均经校验
    check("refinement post-fixpoint verified",
          body.get("fixpoint", {}).get("post_fixpoint_verified") is True)

    # budget=1 时响应形态与未选精化完全一致
    code, b1 = request("POST", "/audit",
                       dict(REFINEMENT_CASE, refinement={"budget": 1}))
    check("budget=1 keeps legacy semantics (still alarm, no partition fields)",
          code == 200 and b1.get("verdict") == "fail"
          and "partitions" not in b1.get("points", {}).get("8", {})
          and "partition_merges" not in b1)

    # 非法精化预算:结构错误合并反馈
    code, body = request("POST", "/audit",
                         dict(REFINEMENT_CASE, refinement={"budget": 9}))
    check("invalid refinement budget rejected with merged error",
          code == 200 and body.get("verdict") == "error"
          and "invalid_refinement" in {e.get("kind") for e in body.get("errors", [])}
          and "points" not in body,
          f"body={body}")

    # 无状态性:结构错误之后再次审计,结论不受既往请求影响
    code, body = request("POST", "/audit", PASS_CASE)
    check("no stale state after error case",
          code == 200 and body.get("verdict") == "pass")

    if _failures:
        print(f"smoke FAILED: {len(_failures)} check(s): {', '.join(_failures)}")
        return 1
    print("smoke OK: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
