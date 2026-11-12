"""输出文件的原子写入工具。

先写入同目录临时文件再 ``os.replace`` 原子替换：只有完整写出并成功
关闭后才替换旧结果；任何中途失败都保留原有输出文件不动。
"""

from __future__ import annotations

import json
import os
import tempfile


def atomic_write_json(path: str, payload: dict) -> None:
    directory = os.path.dirname(os.path.abspath(path))
    os.makedirs(directory, exist_ok=True)
    # delete=False：由我们显式控制临时文件生命周期。
    fd, tmp_path = tempfile.mkstemp(
        prefix=".tmp-", suffix=".json", dir=directory
    )
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False, indent=2)
            fh.write("\n")
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(tmp_path, path)
    except BaseException:
        # 写出失败：清理临时文件，旧输出原封不动。
        try:
            os.unlink(tmp_path)
        except FileNotFoundError:
            pass
        raise
