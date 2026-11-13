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
9. 命令行入口：成功原子替换、失败保留旧结果、inconsistent 正常落盘；
10. 析取方案 alternatives：任务书析取例、不同匹配须选不同方案、
    方案内共享见证、方案见证经键合并触发新匹配、部分方案冲突、
    全部方案冲突、空事实，以及 alternatives 的非法结构/引用/rank
    定位（零基数组下标）；
11. compare_query 包含性：任务书析取例（false -> 补规则后 true）、
    匿名结果（不能仅比当前答案）、常量元组反例、变量各自绑定、
    键合并与可增添匿名行的世界、inconsistent 仅报 inconsistent、
    省略时保持原报告结构、非法 compare_query 字段定位与整次拒绝、
    CLI 落盘；所有反例经独立校验器复核。
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


class TestAlternativesSpecExample(unittest.TestCase):
    """任务书析取例：A(a)，A(x)->B(x)或C(x)，B(x)->D(x)，C(x)->D(x)。"""

    def _payload(self, query_rel):
        return {
            "schema": _schema_r(
                A=(1, [0], [0]),
                B=(1, [0], [0]),
                C=(1, [0], [0]),
                D=(1, [0], [0]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "alternatives": [
                        [{"rel": "B", "args": ["x"]}],
                        [{"rel": "C", "args": ["x"]}],
                    ],
                },
                {
                    "body": [{"rel": "B", "args": ["x"]}],
                    "head": {"rel": "D", "args": ["x"]},
                },
                {
                    "body": [{"rel": "C", "args": ["x"]}],
                    "head": {"rel": "D", "args": ["x"]},
                },
            ],
            "query": {
                "body": [{"rel": query_rel, "args": ["x"]}],
                "project": ["x"],
            },
        }

    def test_conclusion_common_to_all_branches_is_certain(self):
        # 两个分支分别选 B(a)/C(a)，都推出 D(a)，D 的投影必然成立。
        self.assertEqual(
            solve(self._payload("D")), {"status": "ok", "answers": [["a"]]}
        )

    def test_branch_local_choice_is_not_certain(self):
        # B(a)/C(a) 各只在一个分支成立，都不是所有合法世界共有。
        self.assertEqual(
            solve(self._payload("B")), {"status": "ok", "answers": []}
        )
        self.assertEqual(
            solve(self._payload("C")), {"status": "ok", "answers": []}
        )


class TestAlternativesForcedChoice(unittest.TestCase):
    """不同 body 匹配被迫选择不同方案：a 只能选 F，b 只能选 E。"""

    def _payload(self, query_rel):
        return {
            "schema": _schema_r(
                P=(1, [0], [0]),
                D=(2, [0, 0], [0]),
                E=(2, [0, 0], [0]),
                F=(2, [0, 0], [0]),
            ),
            "facts": [
                {"rel": "P", "args": ["a"]},
                {"rel": "P", "args": ["b"]},
                {"rel": "D", "args": ["a", "m"]},
                {"rel": "D", "args": ["b", "n"]},
                {"rel": "E", "args": ["a", "e"]},
                {"rel": "F", "args": ["b", "f"]},
            ],
            "rules": [
                {
                    "body": [
                        {"rel": "P", "args": ["x"]},
                        {"rel": "D", "args": ["x", "y"]},
                    ],
                    "alternatives": [
                        [{"rel": "E", "args": ["x", "y"]}],
                        [{"rel": "F", "args": ["x", "y"]}],
                    ],
                }
            ],
            "query": {
                "body": [{"rel": query_rel, "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
        }

    def test_each_match_picks_the_only_consistent_alternative(self):
        # 绑定 (a,m)：选 E 会与事实 E(a,e) 同键冲突（要求 m=e），只能选
        # F(a,m)；绑定 (b,n)：选 F 会与事实 F(b,f) 冲突（要求 n=f），
        # 只能选 E(b,n)。唯一存活分支同时含两个推导结果。
        self.assertEqual(
            solve(self._payload("E"))["answers"], [["a", "e"], ["b", "n"]]
        )
        self.assertEqual(
            solve(self._payload("F"))["answers"], [["a", "m"], ["b", "f"]]
        )


class TestAlternativeSharedWitness(unittest.TestCase):
    """方案内未在 body 出现的同名变量共享同一存在对象。"""

    def test_shared_existential_joins_within_alternative(self):
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                R=(2, [0, 1], [0, 1]),
                S=(1, [1], [0]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "alternatives": [
                        [
                            {"rel": "R", "args": ["x", "y"]},
                            {"rel": "S", "args": ["y"]},
                        ]
                    ],
                }
            ],
            "query": {
                "body": [
                    {"rel": "R", "args": ["x", "y"]},
                    {"rel": "S", "args": ["y"]},
                ],
                "project": ["x"],
            },
        }
        # y 在 R 与 S 中是同一个匿名对象，连接成立 -> x=a 确定。
        self.assertEqual(solve(payload)["answers"], [["a"]])
        # 但匿名对象本身不能作为答案。
        payload["query"] = {
            "body": [{"rel": "S", "args": ["y"]}],
            "project": ["y"],
        }
        self.assertEqual(solve(payload)["answers"], [])


class TestAlternativeKeyMergeTriggersMatch(unittest.TestCase):
    """方案引入的匿名对象经键合并变成常量后，才触发新的连接匹配。"""

    def _payload(self, query):
        return {
            "schema": _schema_r(
                A=(1, [0], [0]),
                M=(2, [0, 1], [0]),
                Q=(2, [0, 1], [0, 1]),
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
                # 两个方案都含 M(x,y)；方案 2 额外让同一 y 出现在 Q。
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "alternatives": [
                        [{"rel": "M", "args": ["x", "y"]}],
                        [
                            {"rel": "M", "args": ["x", "y"]},
                            {"rel": "Q", "args": ["x", "y"]},
                        ],
                    ],
                },
                # M(a, 匿名) 搬到 R，与事实 R(a,k) 同键 -> 匿名 = k
                {
                    "body": [{"rel": "M", "args": ["x", "y"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                },
                # 匿名合并成 k 后连接 S(k,z1) 才成立 -> T(a,z1)
                {
                    "body": [
                        {"rel": "M", "args": ["x", "y"]},
                        {"rel": "S", "args": ["y", "z"]},
                    ],
                    "head": {"rel": "T", "args": ["x", "z"]},
                },
            ],
            "query": query,
        }

    def test_merge_enables_join_in_every_branch(self):
        payload = self._payload(
            {
                "body": [{"rel": "T", "args": ["x", "z"]}],
                "project": ["x", "z"],
            }
        )
        self.assertEqual(solve(payload)["answers"], [["a", "z1"]])

    def test_branch_local_atom_is_not_certain(self):
        # Q 只在选了方案 2 的分支成立，并非所有合法世界共有。
        payload = self._payload(
            {
                "body": [{"rel": "Q", "args": ["x", "y"]}],
                "project": ["x"],
            }
        )
        self.assertEqual(solve(payload)["answers"], [])


class TestAlternativePartialConflict(unittest.TestCase):
    """部分方案冲突：冲突方案的分支被丢弃，整题并非无解。"""

    def test_conflicting_alternative_does_not_sink_the_problem(self):
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                B=(2, [0, 0], [0]),
                E=(2, [0, 0], [0]),
                F=(2, [0, 0], [0]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "B", "args": ["a", "m"]},
                {"rel": "E", "args": ["a", "e"]},
            ],
            "rules": [
                {
                    "body": [
                        {"rel": "A", "args": ["x"]},
                        {"rel": "B", "args": ["x", "y"]},
                    ],
                    "alternatives": [
                        # 与事实 E(a,e) 同键冲突（要求 m=e），该分支被丢弃
                        [{"rel": "E", "args": ["x", "y"]}],
                        [{"rel": "F", "args": ["x", "y"]}],
                    ],
                }
            ],
            "query": {
                "body": [{"rel": "F", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
        }
        self.assertEqual(
            solve(payload), {"status": "ok", "answers": [["a", "m"]]}
        )


class TestAlternativeAllConflict(unittest.TestCase):
    """全部方案都冲突 -> 没有任何合法世界 -> inconsistent。"""

    def test_all_alternatives_conflicting_is_inconsistent(self):
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                B=(2, [0, 0], [0]),
                E=(2, [0, 0], [0]),
                F=(2, [0, 0], [0]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "B", "args": ["a", "m"]},
                {"rel": "E", "args": ["a", "e"]},
                {"rel": "F", "args": ["a", "f"]},
            ],
            "rules": [
                {
                    "body": [
                        {"rel": "A", "args": ["x"]},
                        {"rel": "B", "args": ["x", "y"]},
                    ],
                    "alternatives": [
                        [{"rel": "E", "args": ["x", "y"]}],  # 要求 m=e
                        [{"rel": "F", "args": ["x", "y"]}],  # 要求 m=f
                    ],
                }
            ],
            "query": {
                "body": [{"rel": "A", "args": ["x"]}],
                "project": ["x"],
            },
        }
        self.assertEqual(solve(payload), {"status": "inconsistent"})


class TestAlternativeEmptyFacts(unittest.TestCase):
    def test_empty_facts_no_binding_no_branching(self):
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                R=(2, [0, 1], [0]),
                S=(2, [0, 1], [0]),
            ),
            "facts": [],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "alternatives": [
                        [{"rel": "R", "args": ["x", "y"]}],
                        [{"rel": "S", "args": ["x", "y"]}],
                    ],
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x"],
            },
        }
        self.assertEqual(solve(payload), {"status": "ok", "answers": []})


class TestAlternativesValidation(unittest.TestCase):
    """alternatives 的非法结构 / 引用 / rank 定位（零基数组下标）。"""

    def _base(self):
        return {
            "schema": _schema_r(
                A=(1, [0], [0]),
                R=(2, [0, 1], [0]),
                S=(2, [0, 1], [0]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "alternatives": [
                        [{"rel": "R", "args": ["x", "y"]}],
                        [{"rel": "S", "args": ["x", "y"]}],
                    ],
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x"],
            },
        }

    def assertRejects(self, payload, path_suffix):
        with self.assertRaises(ValidationError) as ctx:
            solve(payload)
        self.assertTrue(
            ctx.exception.path.endswith(path_suffix),
            f"路径 {ctx.exception.path!r} 应以 {path_suffix!r} 结尾",
        )

    def test_head_and_alternatives_are_mutually_exclusive(self):
        p = self._base()
        p["rules"][0]["head"] = {"rel": "R", "args": ["x", "y"]}
        self.assertRejects(p, "rules[0].alternatives")

    def test_rule_needs_exactly_one_conclusion(self):
        p = self._base()
        del p["rules"][0]["alternatives"]
        self.assertRejects(p, "rules[0].head")

    def test_alternatives_must_be_nonempty_array(self):
        p = self._base()
        p["rules"][0]["alternatives"] = []
        self.assertRejects(p, "rules[0].alternatives")
        p = self._base()
        p["rules"][0]["alternatives"] = {"rel": "R"}
        self.assertRejects(p, "rules[0].alternatives")

    def test_alternative_must_be_nonempty_atom_array(self):
        p = self._base()
        p["rules"][0]["alternatives"] = [[]]
        self.assertRejects(p, "rules[0].alternatives[0]")
        p = self._base()
        p["rules"][0]["alternatives"] = [{"rel": "R", "args": ["x", "y"]}]
        self.assertRejects(p, "rules[0].alternatives[0]")

    def test_unknown_relation_in_alternative(self):
        p = self._base()
        p["rules"][0]["alternatives"][1][0]["rel"] = "Ghost"
        self.assertRejects(p, "rules[0].alternatives[1][0].rel")

    def test_arity_mismatch_in_alternative(self):
        p = self._base()
        p["rules"][0]["alternatives"][0][0]["args"] = ["x"]
        self.assertRejects(p, "rules[0].alternatives[0][0].args")

    def test_non_ascii_variable_in_alternative(self):
        p = self._base()
        p["rules"][0]["alternatives"][0][0]["args"][1] = "变量"
        self.assertRejects(p, "rules[0].alternatives[0][0].args[1]")

    def test_existential_rank_violation_located(self):
        p = self._base()
        p["schema"]["R"]["ranks"] = [0, 0]
        # y 是存在变量，落在 rank0，不高于 body 最高 rank0
        self.assertRejects(p, "rules[0].alternatives[0][0].args[1]")

    def test_shared_var_rank_violation_located(self):
        p = self._base()
        p["schema"]["A"]["ranks"] = [1]
        # x 在 body 的 rank 为 1，方案中 R 首列 rank0 更低
        self.assertRejects(p, "rules[0].alternatives[0][0].args[0]")


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

    def test_alternatives_input_succeeds(self):
        """原文件入口接入 alternatives：任务书析取例经 CLI 求解。"""
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                B=(1, [0], [0]),
                C=(1, [0], [0]),
                D=(1, [0], [0]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "alternatives": [
                        [{"rel": "B", "args": ["x"]}],
                        [{"rel": "C", "args": ["x"]}],
                    ],
                },
                {
                    "body": [{"rel": "B", "args": ["x"]}],
                    "head": {"rel": "D", "args": ["x"]},
                },
                {
                    "body": [{"rel": "C", "args": ["x"]}],
                    "head": {"rel": "D", "args": ["x"]},
                },
            ],
            "query": {
                "body": [{"rel": "D", "args": ["x"]}],
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

    def test_invalid_alternatives_keeps_old_output(self):
        """alternatives 结构非法：整次拒绝并保留旧输出文件。"""
        old_result = {"status": "ok", "answers": [["OLD"]]}
        atomic_write_json(self.output_path, old_result)

        bad = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                R=(2, [0, 1], [0]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "alternatives": [],  # 空方案数组非法
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x"],
            },
        }
        self._write_input(bad)
        proc = self._run_cli()
        self.assertNotEqual(proc.returncode, 0)
        err = json.loads(proc.stderr)
        self.assertTrue(err["path"].endswith("rules[0].alternatives"))
        # 旧结果必须原封不动。
        with open(self.output_path, encoding="utf-8") as fh:
            self.assertEqual(json.load(fh), old_result)


def _match_atoms_world(atoms, rel_facts):
    """显式有限世界上的全部同态匹配（变量 -> 对象名）。"""
    bindings = [{}]
    for atom in atoms:
        next_bindings = []
        for binding in bindings:
            for args in rel_facts.get(atom["rel"], []):
                candidate = dict(binding)
                ok = True
                for var, name in zip(atom["args"], args):
                    if var in candidate:
                        if candidate[var] != name:
                            ok = False
                            break
                    else:
                        candidate[var] = name
                if ok:
                    next_bindings.append(candidate)
        bindings = next_bindings
    return bindings


def _extendable_world(atoms, binding, rel_facts):
    """是否存在延拓 binding 的匹配（未绑定变量可任取世界对象）。"""
    if not atoms:
        return True
    atom, rest = atoms[0], atoms[1:]
    for args in rel_facts.get(atom["rel"], []):
        candidate = dict(binding)
        ok = True
        for var, name in zip(atom["args"], args):
            if var in candidate and candidate[var] != name:
                ok = False
                break
            candidate[var] = name
        if ok and _extendable_world(rest, candidate, rel_facts):
            return True
    return False


def assert_valid_counterexample(case, payload, cx):
    """独立校验 compare_query 反例：结构、合法世界、tuple 命中条件。"""
    case.assertIsInstance(cx, dict)
    case.assertEqual(set(cx), {"objects", "facts", "tuple"})
    objects = cx["objects"]
    case.assertIsInstance(objects, dict)
    case.assertTrue(objects, "objects 不能为空")
    consts = []
    for name, value in objects.items():
        case.assertTrue(
            name and all(ch.isascii() and ch.isalnum() for ch in name),
            f"对象名 {name!r} 须为非空 ASCII 字母数字串",
        )
        case.assertTrue(value is None or isinstance(value, str))
        if value is not None:
            consts.append(value)
    case.assertEqual(len(consts), len(set(consts)), "非 null 值必须唯一")
    input_consts = {c for f in payload["facts"] for c in f["args"]}
    case.assertTrue(
        input_consts <= set(consts), "非 null 值必须覆盖全部输入常量"
    )

    schema = payload["schema"]
    rel_facts = {}
    for fact in cx["facts"]:
        case.assertEqual(set(fact), {"rel", "args"})
        case.assertIn(fact["rel"], schema)
        case.assertEqual(len(fact["args"]), schema[fact["rel"]]["arity"])
        for name in fact["args"]:
            case.assertIn(name, objects)
        rel_facts.setdefault(fact["rel"], []).append(fact["args"])
    for name in cx["tuple"]:
        case.assertIn(name, objects)
    case.assertEqual(len(cx["tuple"]), len(payload["query"]["project"]))

    # 合法世界：包含全部输入事实。
    for fact in payload["facts"]:
        case.assertTrue(
            any(
                wf["rel"] == fact["rel"]
                and all(
                    objects[name] == const
                    for name, const in zip(wf["args"], fact["args"])
                )
                for wf in cx["facts"]
            ),
            f"反例缺少输入事实 {fact}",
        )
    # 键约束：键相同的元组所有列相同。
    for rel, args_list in rel_facts.items():
        by_key = {}
        for args in args_list:
            key = tuple(args[c] for c in schema[rel]["key"])
            case.assertTrue(
                by_key.get(key, args) == args, f"关系 {rel} 键约束被违反"
            )
            by_key[key] = args
    # 全部规则（head 单原子 / alternatives 方案）。
    for rule in payload["rules"]:
        for match in _match_atoms_world(rule["body"], rel_facts):
            if "head" in rule:
                case.assertTrue(
                    _extendable_world([rule["head"]], match, rel_facts),
                    f"规则 head 未满足: {rule}",
                )
            else:
                case.assertTrue(
                    any(
                        _extendable_world(alt, match, rel_facts)
                        for alt in rule["alternatives"]
                    ),
                    f"析取规则无方案满足: {rule}",
                )
    # tuple 命中旧查询而不命中新查询。
    old_results = {
        tuple(b[v] for v in payload["query"]["project"])
        for b in _match_atoms_world(payload["query"]["body"], rel_facts)
    }
    new_results = {
        tuple(b[v] for v in payload["compare_query"]["project"])
        for b in _match_atoms_world(payload["compare_query"]["body"], rel_facts)
    }
    case.assertIn(tuple(cx["tuple"]), old_results)
    case.assertNotIn(tuple(cx["tuple"]), new_results)


class TestCompareSpecExample(unittest.TestCase):
    """任务书 compare_query 例：空事实，一元关系 rank=0 键[0]，
    A(x)->B(x)或C(x)，旧查 A、新查 B。"""

    def _payload(self, with_cb_rule):
        rules = [
            {
                "body": [{"rel": "A", "args": ["x"]}],
                "alternatives": [
                    [{"rel": "B", "args": ["x"]}],
                    [{"rel": "C", "args": ["x"]}],
                ],
            }
        ]
        if with_cb_rule:
            rules.append(
                {
                    "body": [{"rel": "C", "args": ["x"]}],
                    "head": {"rel": "B", "args": ["x"]},
                }
            )
        return {
            "schema": _schema_r(
                A=(1, [0], [0]), B=(1, [0], [0]), C=(1, [0], [0])
            ),
            "facts": [],
            "rules": rules,
            "query": {
                "body": [{"rel": "A", "args": ["x"]}],
                "project": ["x"],
            },
            "compare_query": {
                "body": [{"rel": "B", "args": ["x"]}],
                "project": ["x"],
            },
        }

    def test_disjunctive_choice_breaks_containment(self):
        payload = self._payload(False)
        result = solve(payload)
        self.assertEqual(result["status"], "ok")
        self.assertEqual(result["answers"], [])
        self.assertIs(result["contained"], False)
        assert_valid_counterexample(self, payload, result["counterexample"])

    def test_added_rule_restores_containment(self):
        payload = self._payload(True)
        result = solve(payload)
        self.assertEqual(result["status"], "ok")
        self.assertIs(result["contained"], True)
        self.assertIsNone(result["counterexample"])


class TestCompareAnonymousResults(unittest.TestCase):
    """不能仅比当前答案：两查询 answers 都为空，contained 仍为 false。"""

    def _payload(self, with_copy_rule):
        rules = [
            {
                "body": [{"rel": "A", "args": ["x"]}],
                "head": {"rel": "R", "args": ["x", "y"]},
            }
        ]
        if with_copy_rule:
            rules.append(
                {
                    "body": [{"rel": "R", "args": ["x", "y"]}],
                    "head": {"rel": "S", "args": ["x", "y"]},
                }
            )
        return {
            "schema": _schema_r(
                A=(1, [0], [0]),
                R=(2, [0, 1], [0, 1]),
                S=(2, [0, 1], [0, 1]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": rules,
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
            "compare_query": {
                "body": [{"rel": "S", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
        }

    def test_anonymous_results_still_break_containment(self):
        payload = self._payload(False)
        result = solve(payload)
        # 两查询的常量答案都为空，但合法世界可增添匿名对象与事实。
        self.assertEqual(result["answers"], [])
        self.assertIs(result["contained"], False)
        assert_valid_counterexample(self, payload, result["counterexample"])

    def test_copy_rule_gives_containment(self):
        payload = self._payload(True)
        result = solve(payload)
        self.assertIs(result["contained"], True)
        self.assertIsNone(result["counterexample"])


class TestCompareConstantTuple(unittest.TestCase):
    """常量元组反例：facts R(a)，无规则，旧查 R、新查 S。"""

    def test_counterexample_names_input_constant(self):
        payload = {
            "schema": _schema_r(R=(1, [0], [0]), S=(1, [0], [0])),
            "facts": [{"rel": "R", "args": ["a"]}],
            "rules": [],
            "query": {
                "body": [{"rel": "R", "args": ["x"]}],
                "project": ["x"],
            },
            "compare_query": {
                "body": [{"rel": "S", "args": ["x"]}],
                "project": ["x"],
            },
        }
        result = solve(payload)
        self.assertEqual(result["answers"], [["a"]])
        self.assertIs(result["contained"], False)
        self.assertEqual(
            result["counterexample"],
            {
                "objects": {"o0": "a"},
                "facts": [{"rel": "R", "args": ["o0"]}],
                "tuple": ["o0"],
            },
        )
        assert_valid_counterexample(self, payload, result["counterexample"])


class TestCompareIndependentBinding(unittest.TestCase):
    """两查询变量各自绑定、按投影位置比较。"""

    def _payload(self, compare_body):
        return {
            "schema": _schema_r(
                R=(2, [0, 0], [0, 1]),
                S=(2, [0, 0], [0, 1]),
            ),
            "facts": [{"rel": "R", "args": ["a", "b"]}],
            "rules": [
                {
                    "body": [{"rel": "R", "args": ["x", "y"]}],
                    "head": {"rel": "S", "args": ["x", "y"]},
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x"],
            },
            "compare_query": {
                "body": compare_body,
                "project": ["x"],
            },
        }

    def test_same_name_vars_are_still_independent(self):
        # q2 的 x 同时占两列：S(a,b) 不能证明 S(a,a)。
        payload = self._payload([{"rel": "S", "args": ["x", "x"]}])
        result = solve(payload)
        self.assertIs(result["contained"], False)
        assert_valid_counterexample(self, payload, result["counterexample"])

    def test_positional_projection_gives_containment(self):
        payload = self._payload([{"rel": "S", "args": ["x", "y"]}])
        result = solve(payload)
        self.assertIs(result["contained"], True)
        self.assertIsNone(result["counterexample"])


class TestCompareKeyMerge(unittest.TestCase):
    """冻结体经键合并与常量相等、世界可增添匿名行等情形的包含性。"""

    def _payload(self):
        return {
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
            "compare_query": {
                "body": [{"rel": "B", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
        }

    def test_world_may_add_rows_breaking_containment(self):
        # 合法世界可增添 R 的匿名行，B 覆盖不到。
        payload = self._payload()
        result = solve(payload)
        self.assertIs(result["contained"], False)
        assert_valid_counterexample(self, payload, result["counterexample"])

    def test_rule_backed_containment_holds(self):
        # B(x,z)->R(x,z)：B 的每行都被规则搬进 R。
        payload = self._payload()
        payload["query"] = {
            "body": [{"rel": "B", "args": ["x", "z"]}],
            "project": ["x", "z"],
        }
        payload["compare_query"] = {
            "body": [{"rel": "R", "args": ["x", "y"]}],
            "project": ["x", "y"],
        }
        result = solve(payload)
        self.assertIs(result["contained"], True)
        self.assertIsNone(result["counterexample"])


class TestCompareInconsistent(unittest.TestCase):
    def test_inconsistent_still_reports_only_inconsistent(self):
        payload = {
            "schema": _schema_r(
                R=(2, [0, 1], [0]),
                S=(2, [0, 1], [0]),
            ),
            "facts": [
                {"rel": "R", "args": ["a", "b"]},
                {"rel": "R", "args": ["a", "c"]},
            ],
            "rules": [],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x"],
            },
            "compare_query": {
                "body": [{"rel": "S", "args": ["x", "y"]}],
                "project": ["x"],
            },
        }
        self.assertEqual(solve(payload), {"status": "inconsistent"})


class TestCompareOmitted(unittest.TestCase):
    def test_omitted_compare_query_keeps_old_report_shape(self):
        payload = {
            "schema": _schema_r(Q=(1, [0], [0])),
            "facts": [{"rel": "Q", "args": ["a"]}],
            "rules": [],
            "query": {
                "body": [{"rel": "Q", "args": ["x"]}],
                "project": ["x"],
            },
        }
        result = solve(payload)
        self.assertEqual(result, {"status": "ok", "answers": [["a"]]})
        self.assertNotIn("contained", result)
        self.assertNotIn("counterexample", result)


class TestCompareValidation(unittest.TestCase):
    def _base(self):
        return {
            "schema": _schema_r(
                A=(1, [0], [0]),
                B=(1, [0], [0]),
                C=(2, [0, 1], [0, 1]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [],
            "query": {
                "body": [{"rel": "A", "args": ["x"]}],
                "project": ["x"],
            },
            "compare_query": {
                "body": [{"rel": "B", "args": ["x"]}],
                "project": ["x"],
            },
        }

    def assertRejects(self, payload, path_suffix):
        with self.assertRaises(ValidationError) as ctx:
            solve(payload)
        self.assertTrue(
            ctx.exception.path.endswith(path_suffix),
            f"路径 {ctx.exception.path!r} 应以 {path_suffix!r} 结尾",
        )

    def test_compare_not_object(self):
        p = self._base()
        p["compare_query"] = []
        self.assertRejects(p, "$.compare_query")

    def test_compare_missing_body(self):
        p = self._base()
        del p["compare_query"]["body"]
        self.assertRejects(p, "compare_query.body")

    def test_compare_empty_body(self):
        p = self._base()
        p["compare_query"]["body"] = []
        self.assertRejects(p, "compare_query.body")

    def test_compare_unknown_relation(self):
        p = self._base()
        p["compare_query"]["body"][0]["rel"] = "Ghost"
        self.assertRejects(p, "compare_query.body[0].rel")

    def test_compare_arity_mismatch(self):
        p = self._base()
        p["compare_query"]["body"][0]["args"] = ["x", "y"]
        self.assertRejects(p, "compare_query.body[0].args")

    def test_compare_non_ascii_variable(self):
        p = self._base()
        p["compare_query"]["body"][0]["args"] = ["变量"]
        self.assertRejects(p, "compare_query.body[0].args[0]")

    def test_compare_project_var_not_in_body(self):
        p = self._base()
        p["compare_query"]["project"] = ["z"]
        self.assertRejects(p, "compare_query.project[0]")

    def test_compare_projection_length_mismatch(self):
        p = self._base()
        p["compare_query"] = {
            "body": [{"rel": "C", "args": ["x", "y"]}],
            "project": ["x", "y"],
        }
        self.assertRejects(p, "compare_query.project")

    def test_compare_extra_key(self):
        p = self._base()
        p["compare_query"]["unexpected"] = 1
        self.assertRejects(p, "compare_query.unexpected")


class TestCompareCLI(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="chase-compare-")
        self.input_path = os.path.join(self.tmp, "in.json")
        self.output_path = os.path.join(self.tmp, "out.json")

    def _write_input(self, payload):
        with open(self.input_path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False)

    def _run_cli(self):
        return subprocess.run(
            [sys.executable, "-m", "chase_backend",
             self.input_path, self.output_path],
            cwd=_REPO_ROOT,
            capture_output=True,
            text=True,
        )

    def test_compare_query_written_to_output(self):
        """原文件入口接入 compare_query：任务书析取例经 CLI 求解。"""
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]), B=(1, [0], [0]), C=(1, [0], [0])
            ),
            "facts": [],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "alternatives": [
                        [{"rel": "B", "args": ["x"]}],
                        [{"rel": "C", "args": ["x"]}],
                    ],
                }
            ],
            "query": {
                "body": [{"rel": "A", "args": ["x"]}],
                "project": ["x"],
            },
            "compare_query": {
                "body": [{"rel": "B", "args": ["x"]}],
                "project": ["x"],
            },
        }
        self._write_input(payload)
        proc = self._run_cli()
        self.assertEqual(proc.returncode, 0, proc.stderr)
        with open(self.output_path, encoding="utf-8") as fh:
            result = json.load(fh)
        self.assertEqual(result["status"], "ok")
        self.assertIs(result["contained"], False)
        assert_valid_counterexample(self, payload, result["counterexample"])

    def test_invalid_compare_query_keeps_old_output(self):
        """compare_query 非法：整次拒绝并保留旧输出文件。"""
        old_result = {"status": "ok", "answers": [["OLD"]]}
        atomic_write_json(self.output_path, old_result)
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                B=(1, [0], [0]),
                C=(2, [0, 1], [0, 1]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [],
            "query": {
                "body": [{"rel": "A", "args": ["x"]}],
                "project": ["x"],
            },
            "compare_query": {
                "body": [{"rel": "C", "args": ["x", "y"]}],
                "project": ["x", "y"],  # 投影长度与 query 不一致
            },
        }
        self._write_input(payload)
        proc = self._run_cli()
        self.assertNotEqual(proc.returncode, 0)
        err = json.loads(proc.stderr)
        self.assertTrue(err["path"].endswith("compare_query.project"))
        # 旧结果必须原封不动。
        with open(self.output_path, encoding="utf-8") as fh:
            self.assertEqual(json.load(fh), old_result)


if __name__ == "__main__":
    unittest.main(verbosity=2)
