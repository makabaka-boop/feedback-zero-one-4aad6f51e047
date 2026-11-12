"""独立验收测试（仅依赖标准库 unittest）。

运行方式（在仓库根目录）：

    python -I tests/test_acceptance.py
    # 或
    python -m unittest discover -s tests -t .

覆盖：

1. 题面示例（科研目录缺关联对象，靠键合并补回必然答案）；
2. 递归规则（传递闭包）；
3. 未知对象被键合并后才触发连接；
4. 常量冲突（事实直接冲突 + 规则推导引发冲突）-> inconsistent；
5. 无确定答案（存在对象不得作为答案）；
6. UTF-8 元组序排序与去重；
7. 空事实；
8. 非法输入字段定位与整次拒绝；
9. 命令行入口：成功原子替换、失败保留旧结果、inconsistent 正常落盘。
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest

# 无论以何种方式启动（含 python -I），都先把仓库根目录加入模块搜索路径。
_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from chase_backend import solve  # noqa: E402
from chase_backend.errors import ValidationError  # noqa: E402
from chase_backend.io_utils import atomic_write_json  # noqa: E402


def _schema_r(**kwargs):
    """构造 schema 的小工具：{关系: (arity, ranks, key)}。"""
    return {
        rel: {"arity": a, "ranks": ranks, "key": key}
        for rel, (a, ranks, key) in kwargs.items()
    }


class TestSpecExample(unittest.TestCase):
    """题面原例：A(a)、B(a,b)，两条规则，R 以首列为键。"""

    def test_missing_related_object_recovered_by_key_merge(self):
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                B=(2, [0, 1], [0, 1]),
                R=(2, [0, 1], [0]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "B", "args": ["a", "b"]},
            ],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                },
                {
                    "body": [{"rel": "B", "args": ["x", "z"]}],
                    "head": {"rel": "R", "args": ["x", "z"]},
                },
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
        }
        result = solve(payload)
        self.assertEqual(result, {"status": "ok", "answers": [["a", "b"]]})

    def test_without_merge_info_answer_is_not_definite(self):
        """对照组：没有 B(a,b) 时，第二列只是匿名对象，不能作为答案。"""
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                R=(2, [0, 1], [0]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
        }
        result = solve(payload)
        self.assertEqual(result, {"status": "ok", "answers": []})
        # 但只投影首列时，a 是输入常量，答案确定。
        payload["query"]["project"] = ["x"]
        result = solve(payload)
        self.assertEqual(result, {"status": "ok", "answers": [["a"]]})


class TestRecursion(unittest.TestCase):
    def test_transitive_closure(self):
        payload = {
            "schema": _schema_r(
                Edge=(2, [0, 1], [0, 1]),
                Path=(2, [0, 1], [0, 1]),
            ),
            "facts": [
                {"rel": "Edge", "args": ["1", "2"]},
                {"rel": "Edge", "args": ["2", "3"]},
                {"rel": "Edge", "args": ["3", "4"]},
            ],
            "rules": [
                {
                    "body": [{"rel": "Edge", "args": ["x", "y"]}],
                    "head": {"rel": "Path", "args": ["x", "y"]},
                },
                {
                    "body": [
                        {"rel": "Path", "args": ["x", "z"]},
                        {"rel": "Edge", "args": ["z", "y"]},
                    ],
                    "head": {"rel": "Path", "args": ["x", "y"]},
                },
            ],
            "query": {
                "body": [{"rel": "Path", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
        }
        result = solve(payload)
        self.assertEqual(
            result["answers"],
            [
                ["1", "2"], ["1", "3"], ["1", "4"],
                ["2", "3"], ["2", "4"],
                ["3", "4"],
            ],
        )

    def test_recursive_closure_with_cycle_terminates(self):
        """带环图的传递闭包必须终止且去重。"""
        payload = {
            "schema": _schema_r(
                Edge=(2, [0, 1], [0, 1]),
                Path=(2, [0, 1], [0, 1]),
            ),
            "facts": [
                {"rel": "Edge", "args": ["a", "b"]},
                {"rel": "Edge", "args": ["b", "a"]},
            ],
            "rules": [
                {
                    "body": [{"rel": "Edge", "args": ["x", "y"]}],
                    "head": {"rel": "Path", "args": ["x", "y"]},
                },
                {
                    "body": [
                        {"rel": "Path", "args": ["x", "z"]},
                        {"rel": "Edge", "args": ["z", "y"]},
                    ],
                    "head": {"rel": "Path", "args": ["x", "y"]},
                },
            ],
            "query": {
                "body": [{"rel": "Path", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
        }
        result = solve(payload)
        self.assertEqual(
            sorted(tuple(t) for t in result["answers"]),
            [("a", "a"), ("a", "b"), ("b", "a"), ("b", "b")],
        )


class TestKeyMergeTriggersJoin(unittest.TestCase):
    """未知对象先被键约束合并到常量，合并后才满足另一条规则的连接。"""

    def test_null_merged_then_join_fires(self):
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                R=(2, [0, 1], [0]),
                S=(2, [0, 1], [0, 1]),
                T=(2, [0, 1], [0, 1]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "R", "args": ["a", "k"]},
                {"rel": "S", "args": ["k", "z1"]},
            ],
            "rules": [
                # 生成 R(a, 匿名对象)；与事实 R(a,k) 键相同 -> 匿名对象 = k
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                },
                # 合并前 y 是匿名对象，S(y,z) 无法匹配；
                # 合并使 y=k 后连接成立，推出常量元组 T(a,z1)
                {
                    "body": [
                        {"rel": "R", "args": ["x", "y"]},
                        {"rel": "S", "args": ["y", "z"]},
                    ],
                    "head": {"rel": "T", "args": ["x", "z"]},
                },
            ],
            "query": {
                "body": [{"rel": "T", "args": ["x", "z"]}],
                "project": ["x", "z"],
            },
        }
        result = solve(payload)
        self.assertEqual(result, {"status": "ok", "answers": [["a", "z1"]]})

    def test_null_null_merge_across_tuples(self):
        """两个规则各生成匿名对象，同键合并后再被事实行绑定到常量，连接才成立。"""
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                B=(1, [0], [0]),
                # K 以首列(常量 a)为键：两个匿名第二列 u、v 必须相等
                K=(2, [0, 1], [0]),
                # R 同样以首列为键：事实行 R(a,m) 把合并后的匿名对象绑定到 m
                R=(2, [0, 1], [0]),
                S=(2, [1, 1], [0, 1]),
                T=(2, [1, 1], [0, 1]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "B", "args": ["a"]},
                {"rel": "R", "args": ["a", "m"]},
                {"rel": "S", "args": ["m", "q"]},
            ],
            "rules": [
                # K(a, 匿名 u)
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "K", "args": ["x", "u"]},
                },
                # K(a, 匿名 v)：与上一行同键 -> u = v
                {
                    "body": [{"rel": "B", "args": ["x"]}],
                    "head": {"rel": "K", "args": ["x", "v"]},
                },
                # 把合并后的匿名对象搬到 R：与事实 R(a,m) 同键 -> 匿名 = m
                {
                    "body": [{"rel": "K", "args": ["x", "w"]}],
                    "head": {"rel": "R", "args": ["x", "w"]},
                },
                # 匿名对象变成常量 m 后，与 S(m,q) 连接成立 -> T(a,q)
                {
                    "body": [
                        {"rel": "R", "args": ["x", "y"]},
                        {"rel": "S", "args": ["y", "z"]},
                    ],
                    "head": {"rel": "T", "args": ["x", "z"]},
                },
            ],
            "query": {
                "body": [{"rel": "T", "args": ["x", "z"]}],
                "project": ["x", "z"],
            },
        }
        result = solve(payload)
        self.assertEqual(result, {"status": "ok", "answers": [["a", "q"]]})


class TestInconsistent(unittest.TestCase):
    def test_direct_fact_constant_conflict(self):
        payload = {
            "schema": _schema_r(R=(2, [0, 1], [0])),
            "facts": [
                {"rel": "R", "args": ["a", "b"]},
                {"rel": "R", "args": ["a", "c"]},
            ],
            "rules": [],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x"],
            },
        }
        self.assertEqual(solve(payload), {"status": "inconsistent"})

    def test_rule_derived_constant_conflict(self):
        """事实 R(a,b) 与规则推出的 R(a,c) 在同一键上常量冲突。"""
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                C=(2, [0, 1], [0, 1]),
                R=(2, [0, 1], [0]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "C", "args": ["a", "c"]},
                {"rel": "R", "args": ["a", "b"]},
            ],
            "rules": [
                {
                    "body": [
                        {"rel": "A", "args": ["x"]},
                        {"rel": "C", "args": ["x", "y"]},
                    ],
                    "head": {"rel": "R", "args": ["x", "y"]},
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x"],
            },
        }
        self.assertEqual(solve(payload), {"status": "inconsistent"})

    def test_distinct_string_constants_never_equal(self):
        """即使经过多轮合并，两个不同常量被要求相等仍是 inconsistent。"""
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                R=(3, [0, 1, 2], [0, 1]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "R", "args": ["a", "k", "b"]},
                {"rel": "R", "args": ["a", "k", "c"]},
            ],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y", "z"]},
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y", "z"]}],
                "project": ["x"],
            },
        }
        self.assertEqual(solve(payload), {"status": "inconsistent"})


class TestNoDefiniteAnswer(unittest.TestCase):
    def test_existential_only_gives_no_constant_answer(self):
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                R=(2, [0, 1], [0]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
        }
        self.assertEqual(solve(payload)["answers"], [])

    def test_partial_anonymous_component_excludes_whole_tuple(self):
        """任一分量不是输入常量，整个元组都不能作为答案。"""
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                R=(2, [0, 1], [0, 1]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
        }
        self.assertEqual(solve(payload)["answers"], [])


class TestOrderingAndEmpty(unittest.TestCase):
    def test_utf8_tuple_order_and_dedup(self):
        words = ["中", "a", "é", "Z", "12", "a"]  # 含重复事实
        payload = {
            "schema": _schema_r(Q=(1, [0], [0])),
            "facts": [{"rel": "Q", "args": [w]} for w in words],
            "rules": [],
            "query": {
                "body": [{"rel": "Q", "args": ["x"]}],
                "project": ["x"],
            },
        }
        result = solve(payload)
        expected = sorted(
            set(words), key=lambda s: s.encode("utf-8")
        )
        self.assertEqual(result["answers"], [[w] for w in expected])
        self.assertEqual(
            expected, ["12", "Z", "a", "é", "中"]
        )

    def test_empty_facts_is_legal(self):
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                R=(2, [0, 1], [0]),
            ),
            "facts": [],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x"],
            },
        }
        self.assertEqual(solve(payload), {"status": "ok", "answers": []})

    def test_unicode_constants_distinct(self):
        payload = {
            "schema": _schema_r(R=(2, [0, 1], [0])),
            "facts": [
                {"rel": "R", "args": ["你好", "世界"]},
                {"rel": "R", "args": ["你好", "世界！"]},
            ],
            "rules": [],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
        }
        self.assertEqual(solve(payload), {"status": "inconsistent"})


class TestValidation(unittest.TestCase):
    def _base(self):
        return {
            "schema": _schema_r(
                A=(1, [0], [0]),
                R=(2, [0, 1], [0]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
        }

    def assertRejects(self, payload, path_suffix):
        with self.assertRaises(ValidationError) as ctx:
            solve(payload)
        self.assertTrue(
            ctx.exception.path.endswith(path_suffix),
            f"路径 {ctx.exception.path!r} 应以 {path_suffix!r} 结尾",
        )

    def test_bool_rejected_as_integer(self):
        p = self._base()
        p["schema"]["A"]["arity"] = True
        self.assertRejects(p, "schema.A.arity")

    def test_negative_and_float_arity_rejected(self):
        p = self._base()
        p["schema"]["A"]["arity"] = 0
        self.assertRejects(p, "schema.A.arity")
        p = self._base()
        p["schema"]["A"]["arity"] = 1.5
        self.assertRejects(p, "schema.A.arity")

    def test_ranks_length_mismatch(self):
        p = self._base()
        p["schema"]["R"]["ranks"] = [0]
        self.assertRejects(p, "schema.R.ranks")

    def test_negative_rank_and_bool_rank(self):
        p = self._base()
        p["schema"]["R"]["ranks"] = [0, -1]
        self.assertRejects(p, "schema.R.ranks[1]")
        p = self._base()
        p["schema"]["R"]["ranks"] = [0, True]
        self.assertRejects(p, "schema.R.ranks[1]")

    def test_empty_and_duplicate_and_out_of_range_key(self):
        p = self._base()
        p["schema"]["R"]["key"] = []
        self.assertRejects(p, "schema.R.key")
        p = self._base()
        p["schema"]["R"]["key"] = [0, 0]
        self.assertRejects(p, "schema.R.key[1]")
        p = self._base()
        p["schema"]["R"]["key"] = [5]
        self.assertRejects(p, "schema.R.key[0]")

    def test_unknown_relation_reference(self):
        p = self._base()
        p["facts"][0]["rel"] = "Ghost"
        self.assertRejects(p, "facts[0].rel")

    def test_arity_mismatch(self):
        p = self._base()
        p["facts"][0]["args"] = ["a", "b"]
        self.assertRejects(p, "facts[0].args")

    def test_non_string_constant_rejected(self):
        p = self._base()
        p["facts"][0]["args"] = [1]
        self.assertRejects(p, "facts[0].args[0]")

    def test_non_ascii_variable_name(self):
        p = self._base()
        p["rules"][0]["head"]["args"][1] = "变量"
        self.assertRejects(p, "rules[0].head.args[1]")

    def test_empty_body_rejected(self):
        p = self._base()
        p["rules"][0]["body"] = []
        self.assertRejects(p, "rules[0].body")

    def test_shared_var_rank_violation(self):
        # R ranks 改成 [1,1]：x 在 A 的 rank0，head 列 rank1 仍合法；
        # 构造 x 的 head 列 rank 低于 body 位置：
        p = self._base()
        p["schema"]["R"]["ranks"] = [0, 0]
        # 存在变量 y 落在 rank0，不高于 body 最高 rank0，应被拒绝
        self.assertRejects(p, "rules[0].head.args[1]")

    def test_existential_rank_must_be_strictly_higher(self):
        p = self._base()
        p["schema"]["R"]["ranks"] = [0, 0]
        self.assertRejects(p, "rules[0].head.args[1]")

    def test_project_var_not_in_body(self):
        p = self._base()
        p["query"]["project"] = ["x", "z"]
        self.assertRejects(p, "query.project[1]")

    def test_missing_top_level_field(self):
        p = self._base()
        del p["rules"]
        self.assertRejects(p, "$.rules")

    def test_extra_top_level_field(self):
        p = self._base()
        p["unexpected"] = 1
        self.assertRejects(p, "unexpected")

    def test_wrong_top_level_type(self):
        with self.assertRaises(ValidationError) as ctx:
            solve([])
        self.assertEqual(ctx.exception.path, "$")

    def test_empty_project_rejected(self):
        p = self._base()
        p["query"]["project"] = []
        self.assertRejects(p, "query.project")


class TestCLI(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="chase-accept-")
        self.input_path = os.path.join(self.tmp, "in.json")
        self.output_path = os.path.join(self.tmp, "out.json")

    def _write_input(self, payload):
        with open(self.input_path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False)

    def _run_cli(self):
        # 本仓库代码为受信代码，直接以 -m 方式从仓库根目录启动。
        proc = subprocess.run(
            [sys.executable, "-m", "chase_backend",
             self.input_path, self.output_path],
            cwd=_REPO_ROOT,
            capture_output=True,
            text=True,
        )
        return proc

    def test_success_replaces_output(self):
        payload = {
            "schema": _schema_r(Q=(1, [0], [0])),
            "facts": [{"rel": "Q", "args": ["a"]}],
            "rules": [],
            "query": {
                "body": [{"rel": "Q", "args": ["x"]}],
                "project": ["x"],
            },
        }
        self._write_input(payload)
        proc = self._run_cli()
        self.assertEqual(proc.returncode, 0, proc.stderr)
        with open(self.output_path, encoding="utf-8") as fh:
            self.assertEqual(
                json.load(fh), {"status": "ok", "answers": [["a"]]}
            )

    def test_invalid_input_keeps_old_output(self):
        # 先写一份合法的旧结果。
        old_result = {"status": "ok", "answers": [["OLD"]]}
        atomic_write_json(self.output_path, old_result)

        bad = {
            "schema": _schema_r(Q=(1, [0], [0])),
            "facts": [{"rel": "Q", "args": [1]}],  # 常量必须是字符串
            "rules": [],
            "query": {
                "body": [{"rel": "Q", "args": ["x"]}],
                "project": ["x"],
            },
        }
        self._write_input(bad)
        proc = self._run_cli()
        self.assertNotEqual(proc.returncode, 0)
        err = json.loads(proc.stderr)
        self.assertTrue(err["path"].endswith("facts[0].args[0]"))
        # 旧结果必须原封不动。
        with open(self.output_path, encoding="utf-8") as fh:
            self.assertEqual(json.load(fh), old_result)

    def test_inconsistent_is_written_as_success(self):
        payload = {
            "schema": _schema_r(R=(2, [0, 1], [0])),
            "facts": [
                {"rel": "R", "args": ["a", "b"]},
                {"rel": "R", "args": ["a", "c"]},
            ],
            "rules": [],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x"],
            },
        }
        self._write_input(payload)
        proc = self._run_cli()
        self.assertEqual(proc.returncode, 0, proc.stderr)
        with open(self.output_path, encoding="utf-8") as fh:
            self.assertEqual(json.load(fh), {"status": "inconsistent"})

    def test_missing_input_file_fails_without_output(self):
        proc = subprocess.run(
            [sys.executable, "-m", "chase_backend",
             os.path.join(self.tmp, "nope.json"), self.output_path],
            cwd=_REPO_ROOT,
            capture_output=True,
            text=True,
        )
        self.assertNotEqual(proc.returncode, 0)
        self.assertFalse(os.path.exists(self.output_path))


if __name__ == "__main__":
    unittest.main(verbosity=2)
