"""共享的迁移函数与断言蕴含判定。

单分区引擎(app.analyzer)与有限精化分区引擎(app.partitioning)复用同一套
精确语义,保证两种模式下八边形迁移、收窄与包线核对的结果一致。
"""
from __future__ import annotations

from .octagon import Octagon, neg_terms, terms_text


def apply_action(state: Octagon, action: tuple) -> "Octagon | None":
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


def bound_detail(state: Octagon, terms: tuple, k: int, disjunction: bool = False) -> dict:
    b = state.bound(terms) if terms else 0
    detail = {
        "text": f"{terms_text(terms)} <= {k}",
        "bound": None if b == float("inf") else b,
        "required": k,
        "implied": b <= k,
    }
    if disjunction:
        detail["disjunction"] = True
    return detail


def check_assertion(state: Octagon, cond) -> tuple:
    """返回 (是否被蕴含, 逐条件界信息)。!= 以两个析取支检查。"""
    terms, kind, k = cond.terms, cond.kind, cond.k
    if kind == "le":
        details = [bound_detail(state, terms, k)]
        return details[0]["implied"], details
    if kind == "eq":
        details = [
            bound_detail(state, terms, k),
            bound_detail(state, neg_terms(terms), -k),
        ]
        return all(d["implied"] for d in details), details
    # ne:expr <= k-1 或 -expr <= -k-1 任一成立即蕴含
    details = [
        bound_detail(state, terms, k - 1, disjunction=True),
        bound_detail(state, neg_terms(terms), -k - 1, disjunction=True),
    ]
    return any(d["implied"] for d in details), details
