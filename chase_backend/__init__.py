"""后端交换作业：带键约束与存在量词规则的 chase 推理后端。

对外主入口为 :func:`chase_backend.solve`，命令行入口见
``python -m chase_backend``。
"""

from .errors import ChaseError, InconsistentError, ValidationError
from .solver import solve

__all__ = ["solve", "ChaseError", "InconsistentError", "ValidationError"]
