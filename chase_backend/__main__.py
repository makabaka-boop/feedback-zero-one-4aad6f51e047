"""命令行入口：``python -m chase_backend INPUT OUTPUT``。

约定：

* 输入文件读取或校验/求解失败时，进程以非零码退出，**不会**创建或
  覆盖输出文件（旧结果完整保留），错误信息以 JSON 打到 stderr；
* 只有完整求解并成功原子落盘后才正常退出（退出码 0）。
  ``inconsistent`` 属于求解成功的一种正常结果，同样会替换输出。
"""

from __future__ import annotations

import json
import sys

from .errors import ChaseError, ValidationError
from .io_utils import atomic_write_json
from .solver import solve


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if len(argv) != 2:
        print(
            json.dumps(
                {
                    "error": "用法: python -m chase_backend INPUT OUTPUT",
                    "path": "$",
                },
                ensure_ascii=False,
            ),
            file=sys.stderr,
        )
        return 2

    input_path, output_path = argv
    try:
        with open(input_path, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
    except FileNotFoundError:
        print(
            json.dumps(
                {"error": f"输入文件不存在: {input_path}", "path": "$"},
                ensure_ascii=False,
            ),
            file=sys.stderr,
        )
        return 1
    except json.JSONDecodeError as exc:
        print(
            json.dumps(
                {"error": f"输入不是合法 JSON: {exc.msg}", "path": "$"},
                ensure_ascii=False,
            ),
            file=sys.stderr,
        )
        return 1

    try:
        result = solve(payload)
    except ValidationError as exc:
        print(
            json.dumps(
                {"error": exc.message, "path": exc.path}, ensure_ascii=False
            ),
            file=sys.stderr,
        )
        return 1
    except ChaseError as exc:  # 防御：其余引擎异常也不得污染输出
        print(
            json.dumps({"error": str(exc), "path": "$"}, ensure_ascii=False),
            file=sys.stderr,
        )
        return 1

    # 只有走到这里才触碰输出路径：原子替换，旧文件在替换前不受影响。
    atomic_write_json(output_path, result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
