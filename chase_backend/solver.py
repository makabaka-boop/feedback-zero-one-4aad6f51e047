"""顶层求解编排：校验 -> 析取 chase -> 各合法世界共有的查询答案。"""

from __future__ import annotations

from typing import Any

from .engine import chase_all
from .validator import validate


def solve(payload: Any) -> dict:
    """求解一份完整输入。

    返回：

    * ``{"status": "ok", "answers": [[...], ...]}`` —— 合法且求解成功，
      答案为所有合法世界（全部自洽 chase 分支）共有的常量投影元组，
      去重后按 UTF-8 元组字典序排列；
    * ``{"status": "inconsistent"}`` —— 无任何合法世界（所有分支都
      因键约束要求两个不同常量相等而冲突）。

    输入非法时抛出 :class:`~chase_backend.errors.ValidationError`，
    由调用方负责整次拒绝并保留旧输出。
    """
    problem = validate(payload)
    branches = chase_all(problem["schema"], problem["facts"], problem["rules"])
    if not branches:
        return {"status": "inconsistent"}
    # 必然答案 = 各存活分支常量答案的交集。
    common: set[tuple[str, ...]] | None = None
    for branch in branches:
        answers = set(branch.answer_query(problem["query"]))
        common = answers if common is None else (common & answers)
        if not common:
            break
    ordered = sorted(
        common if common is not None else set(),
        key=lambda t: tuple(s.encode("utf-8") for s in t),
    )
    return {"status": "ok", "answers": [list(t) for t in ordered]}
