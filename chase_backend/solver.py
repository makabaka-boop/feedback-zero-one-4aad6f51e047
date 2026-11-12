"""顶层求解编排：校验 -> chase -> 查询，统一输出结构。"""

from __future__ import annotations

from typing import Any

from .engine import ChaseEngine
from .errors import InconsistentError
from .validator import validate


def solve(payload: Any) -> dict:
    """求解一份完整输入。

    返回：

    * ``{"status": "ok", "answers": [[...], ...]}`` —— 合法且求解成功；
    * ``{"status": "inconsistent"}`` —— 无任何合法世界。

    输入非法时抛出 :class:`~chase_backend.errors.ValidationError`，
    由调用方负责整次拒绝并保留旧输出。
    """
    problem = validate(payload)
    engine = ChaseEngine(
        problem["schema"], problem["facts"], problem["rules"]
    )
    try:
        engine.run()
    except InconsistentError:
        return {"status": "inconsistent"}
    answers = engine.answer_query(problem["query"])
    return {"status": "ok", "answers": [list(t) for t in answers]}
