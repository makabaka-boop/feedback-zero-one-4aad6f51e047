"""本包使用的异常类型。"""


class ChaseError(Exception):
    """所有本包自定义异常的基类。"""


class ValidationError(ChaseError):
    """非法输入异常。

    ``path`` 为定位到具体字段的 JSON 路径（如 ``rules[0].head.arity``），
    便于调用方整次拒绝时向用户指明出错位置。
    """

    def __init__(self, message: str, path: str = "$"):
        self.path = path
        self.message = message
        super().__init__(f"{path}: {message}")


class InconsistentError(ChaseError):
    """不存在任何合法世界（键约束导致两个不同常量必须相等）。"""
