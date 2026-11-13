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
11. 封闭关系 closed_relations：任务书封闭例（含删除事实 -> inconsistent）、
    多候选但无确定取值、共享存在对象的跨关系矛盾、封闭绑定经键合并
    触发新匹配、禁止逐列拼接（见证必须整体对应一条输入元组）、
    析取方案部分失效与全部失效、空事实、省略/空数组兼容、非法声明
    字段路径定位（含零基数组下标），以及 CLI 接入与非法声明保留旧文件。
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


class TestClosedRelationsSpecExample(unittest.TestCase):
    """任务书封闭例：A、C 一元，R 二元，rank [0]/[1]/[0,1]，键均为首列。

    事实 A(a)、C(b)；规则 A(x)->R(x,y)、R(x,y)->C(y)；封闭 C 后
    查询 R 两列得 [["a","b"]]；删除 C(b) 则 inconsistent。
    """

    def _payload(self, include_c_fact):
        facts = [{"rel": "A", "args": ["a"]}]
        if include_c_fact:
            facts.append({"rel": "C", "args": ["b"]})
        return {
            "schema": _schema_r(
                A=(1, [0], [0]),
                C=(1, [1], [0]),
                R=(2, [0, 1], [0]),
            ),
            "facts": facts,
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                },
                {
                    "body": [{"rel": "R", "args": ["x", "y"]}],
                    "head": {"rel": "C", "args": ["y"]},
                },
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
            "closed_relations": ["C"],
        }

    def test_closed_relation_pins_existential_to_fact(self):
        self.assertEqual(
            solve(self._payload(True)),
            {"status": "ok", "answers": [["a", "b"]]},
        )

    def test_deleting_closed_fact_makes_inconsistent(self):
        self.assertEqual(
            solve(self._payload(False)), {"status": "inconsistent"}
        )

    def test_omitted_and_empty_array_keep_relations_open(self):
        # 省略字段：C 开放，存在对象不绑定 b，R 两列无常量答案。
        payload = self._payload(True)
        del payload["closed_relations"]
        self.assertEqual(solve(payload), {"status": "ok", "answers": []})
        # 显式空数组与省略等价。
        payload["closed_relations"] = []
        self.assertEqual(solve(payload), {"status": "ok", "answers": []})


class TestClosedMultipleCandidatesNoDefiniteValue(unittest.TestCase):
    """多候选但无确定取值：存在对象可取两个封闭事实常量之一。"""

    def _payload(self):
        return {
            "schema": _schema_r(
                A=(1, [0], [0]),
                S=(1, [1], [0]),
                R=(2, [0, 1], [0, 1]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "S", "args": ["s1"]},
                {"rel": "S", "args": ["s2"]},
            ],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                },
                {
                    "body": [{"rel": "R", "args": ["x", "y"]}],
                    "head": {"rel": "S", "args": ["y"]},
                },
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
            "closed_relations": ["S"],
        }

    def test_two_witness_branches_no_definite_pair(self):
        # y 可为 s1 或 s2，两个合法世界的 R 两列答案不同 -> 无必然元组。
        self.assertEqual(
            solve(self._payload()), {"status": "ok", "answers": []}
        )

    def test_closed_relation_itself_still_exposes_both_facts(self):
        # 封闭关系 S 的两条事实在每个合法世界都在，查询 S 两值都确定。
        payload = self._payload()
        payload["query"] = {
            "body": [{"rel": "S", "args": ["y"]}],
            "project": ["y"],
        }
        self.assertEqual(
            solve(payload),
            {"status": "ok", "answers": [["s1"], ["s2"]]},
        )

    def test_first_column_still_certain(self):
        payload = self._payload()
        payload["query"]["project"] = ["x"]
        self.assertEqual(
            solve(payload), {"status": "ok", "answers": [["a"]]}
        )


class TestClosedCrossRelationContradiction(unittest.TestCase):
    """共享存在对象进入两个封闭关系，各自只允许不同常量 -> 矛盾。"""

    def _payload(self, p_fact, q_fact, closed):
        return {
            "schema": _schema_r(
                A=(1, [0], [0]),
                P=(1, [1], [0]),
                Q=(1, [1], [0]),
                R=(2, [0, 1], [0, 1]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "P", "args": [p_fact]},
                {"rel": "Q", "args": [q_fact]},
            ],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                },
                {
                    "body": [{"rel": "R", "args": ["x", "y"]}],
                    "head": {"rel": "P", "args": ["y"]},
                },
                {
                    "body": [{"rel": "R", "args": ["x", "y"]}],
                    "head": {"rel": "Q", "args": ["y"]},
                },
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x"],
            },
            "closed_relations": closed,
        }

    def test_same_witness_forced_to_two_distinct_constants(self):
        payload = self._payload("p", "q", ["P", "Q"])
        self.assertEqual(solve(payload), {"status": "inconsistent"})

    def test_shared_constant_is_consistent(self):
        # 两个封闭关系都允许同一常量 p -> 同一见证绑定，自洽。
        payload = self._payload("p", "p", ["P", "Q"])
        self.assertEqual(
            solve(payload), {"status": "ok", "answers": [["a"]]}
        )

    def test_opening_one_relation_removes_contradiction(self):
        # 只封闭 P：Q 开放可自由扩充匿名 y，不再有矛盾。
        payload = self._payload("p", "q", ["P"])
        self.assertEqual(
            solve(payload), {"status": "ok", "answers": [["a"]]}
        )


class TestClosedMergeTriggersMatch(unittest.TestCase):
    """封闭关系把存在对象绑定为常量，合并后触发另一条规则的新连接。"""

    def test_binding_propagates_into_join(self):
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                C=(1, [1], [0]),
                K=(2, [0, 1], [0, 1]),
                R=(2, [0, 1], [0]),
                T=(2, [1, 1], [0, 1]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "C", "args": ["c"]},
                {"rel": "K", "args": ["a", "k"]},
            ],
            "rules": [
                # R(a, 匿名 y)
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                },
                # 封闭 C 只含 c -> y 必须绑定 c
                {
                    "body": [{"rel": "R", "args": ["x", "y"]}],
                    "head": {"rel": "C", "args": ["y"]},
                },
                # 合并后 R(a,c) 与 K(a,k) 连接 -> T(c,k)
                {
                    "body": [
                        {"rel": "R", "args": ["x", "y"]},
                        {"rel": "K", "args": ["x", "z"]},
                    ],
                    "head": {"rel": "T", "args": ["y", "z"]},
                },
            ],
            "query": {
                "body": [{"rel": "T", "args": ["y", "z"]}],
                "project": ["y", "z"],
            },
            "closed_relations": ["C"],
        }
        self.assertEqual(
            solve(payload), {"status": "ok", "answers": [["c", "k"]]}
        )


class TestClosedWholeTupleWitness(unittest.TestCase):
    """封闭关系中的匿名元组必须整体对应一条输入元组，禁止逐列拼接。"""

    def _payload(self, add_k=False, add_spliced_fact=False):
        facts = [
            {"rel": "A", "args": ["a"]},
            {"rel": "F", "args": ["p", "1"]},
            {"rel": "F", "args": ["q", "2"]},
            {"rel": "G", "args": ["q"]},
        ]
        closed = ["F", "G"]
        rules = [
            # 开放 H 承载同一对存在对象 (u, v)
            {
                "body": [{"rel": "A", "args": ["x"]}],
                "head": {"rel": "H", "args": ["u", "v"]},
            },
            # H->封闭 F：(u,v) 必须整体等于 F 的某条事实行
            {
                "body": [{"rel": "H", "args": ["u", "v"]}],
                "head": {"rel": "F", "args": ["u", "v"]},
            },
            # 封闭 G 只含 q -> u=q，整体候选只剩 F(q,2)
            {
                "body": [{"rel": "H", "args": ["u", "v"]}],
                "head": {"rel": "G", "args": ["u"]},
            },
        ]
        if add_k:
            facts.append({"rel": "K", "args": ["1"]})
            closed.append("K")
            # 封闭 K 只含 1 -> v=1；与 u=q 联立要求 F 存在 (q,1) 整体行
            rules.append(
                {
                    "body": [{"rel": "H", "args": ["u", "v"]}],
                    "head": {"rel": "K", "args": ["v"]},
                }
            )
        if add_spliced_fact:
            facts.append({"rel": "F", "args": ["q", "1"]})
        return {
            "schema": _schema_r(
                A=(1, [0], [0]),
                H=(2, [1, 2], [0, 1]),
                F=(2, [1, 2], [0, 1]),
                G=(1, [1], [0]),
                K=(1, [2], [0]),
            ),
            "facts": facts,
            "rules": rules,
            "query": {
                "body": [{"rel": "H", "args": ["u", "v"]}],
                "project": ["u", "v"],
            },
            "closed_relations": closed,
        }

    def test_witness_matches_one_whole_input_tuple(self):
        self.assertEqual(
            solve(self._payload()),
            {"status": "ok", "answers": [["q", "2"]]},
        )

    def test_column_wise_splicing_is_rejected(self):
        # u=q（来自第 2 行）与 v=1（来自第 1 行）的拼接不是任何整体行，
        # 禁止逐列拼接 -> 没有合法世界。
        self.assertEqual(
            solve(self._payload(add_k=True)),
            {"status": "inconsistent"},
        )

    def test_adding_the_whole_row_restores_consistency(self):
        # 补上整体行 F(q,1) 后同一组约束自洽，H 见证确定为 (q,1)。
        self.assertEqual(
            solve(self._payload(add_k=True, add_spliced_fact=True)),
            {"status": "ok", "answers": [["q", "1"]]},
        )


class TestClosedSkolemBranchIsolation(unittest.TestCase):
    """多候选封闭分裂后，各分支的 Skolem 存在对象必须相互隔离。

    确定性规则经 Skolem 缓存复用同一组空对象；封闭关系多候选分裂时，
    若子分支原样共享缓存中的空对象 id，一个分支把它绑定到常量 p 后，
    另一分支再要求它等于 q 就会产生跨分支的伪常量冲突，错误地判
    inconsistent。这里回归该问题：两个封闭事实行的首列都在另一个封闭
    关系中时，两个见证分支都应存活。
    """

    def _payload(self):
        return {
            "schema": _schema_r(
                A=(1, [0], [0]),
                F=(2, [1, 2], [0, 1]),
                G=(1, [1], [0]),
                H=(2, [1, 2], [0, 1]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "F", "args": ["q", "2"]},
                {"rel": "F", "args": ["p", "1"]},
                {"rel": "G", "args": ["q"]},
                {"rel": "G", "args": ["p"]},
            ],
            "rules": [
                # 造全匿名 H(y,z)，Skolem 缓存键为空元组，最易触发共享
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "H", "args": ["y", "z"]},
                },
                # H 进封闭 F：两个整体候选 -> 分裂
                {
                    "body": [{"rel": "H", "args": ["y", "z"]}],
                    "head": {"rel": "F", "args": ["y", "z"]},
                },
                # 两个候选首列 q、p 都在封闭 G 中 -> 两分支都应存活
                {
                    "body": [{"rel": "F", "args": ["y", "z"]}],
                    "head": {"rel": "G", "args": ["y"]},
                },
            ],
            "query": {
                "body": [{"rel": "H", "args": ["y", "z"]}],
                "project": ["y", "z"],
            },
            "closed_relations": ["F", "G"],
        }

    def test_two_witness_branches_both_survive(self):
        # 两分支见证不同（(q,2) 与 (p,1)），H 无共同的确定两列答案。
        self.assertEqual(
            solve(self._payload()), {"status": "ok", "answers": []}
        )

    def test_closed_relation_facts_remain_certain(self):
        payload = self._payload()
        payload["query"] = {
            "body": [{"rel": "F", "args": ["y", "z"]}],
            "project": ["y", "z"],
        }
        self.assertEqual(
            solve(payload),
            {"status": "ok", "answers": [["p", "1"], ["q", "2"]]},
        )

    def test_restricting_one_witness_pins_the_other(self):
        # 去掉 (p,1) 见证与 G(p)：F 只剩 (q,2) 一个整体候选，H 被钉为
        # 该值。注意 F 的输入事实行本身也会触发 F->G，因此两行要一起
        # 移除，否则残留的 F(p,1) 仍会要求封闭 G 含 p。
        payload = self._payload()
        payload["facts"] = [
            f for f in payload["facts"]
            if not (
                (f["rel"] == "G" and f["args"] == ["p"])
                or (f["rel"] == "F" and f["args"] == ["p", "1"])
            )
        ]
        self.assertEqual(
            solve(payload),
            {"status": "ok", "answers": [["q", "2"]]},
        )


class TestClosedAlternativeAtomicExpansion(unittest.TestCase):
    """方案内含封闭关系原子时必须一次性展开，避免同一绑定反复分裂。

    旧实现按原子顺序物化方案，封闭原子多候选会在中途挂起，使排在
    后面的开放原子永远写不进去、方案永远不满足，导致同一
    ``(规则, 绑定)`` 被反复分裂、反复造空对象而不终止。这里用带
    看门狗的求解回归该问题。
    """

    def setUp(self):
        import signal

        def _handler(signum, frame):
            raise AssertionError("方案展开未终止：封闭原子重复分裂")

        self._handler = _handler
        signal.signal(signal.SIGALRM, _handler)
        signal.alarm(15)
        self.addCleanup(signal.alarm, 0)

    def test_multi_candidate_closed_atom_with_open_atom(self):
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                S=(1, [1], [0]),
                R=(2, [0, 1], [0, 1]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "S", "args": ["s1"]},
                {"rel": "S", "args": ["s2"]},
            ],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "alternatives": [
                        [
                            {"rel": "R", "args": ["x", "z"]},
                            {"rel": "S", "args": ["z"]},
                        ]
                    ],
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "z"]}],
                "project": ["x", "z"],
            },
            "closed_relations": ["S"],
        }
        # z 可取 s1 或 s2，两个分支的两列答案不同 -> 无必然元组。
        self.assertEqual(
            solve(payload), {"status": "ok", "answers": []}
        )
        # 只投影首列：两个分支都含 R(a,·)，a 确定。
        payload["query"]["project"] = ["x"]
        self.assertEqual(
            solve(payload), {"status": "ok", "answers": [["a"]]}
        )

    def test_two_closed_atoms_cartesian_product_empty_intersection(self):
        # 同一方案两个封闭原子：候选取笛卡尔积，交集为空时整体失效。
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                S=(1, [1], [0]),
                T=(1, [1], [0]),
                R=(2, [0, 1], [0, 1]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "S", "args": ["s1"]},
                {"rel": "S", "args": ["s2"]},
                {"rel": "T", "args": ["t1"]},
            ],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "alternatives": [
                        [
                            {"rel": "R", "args": ["x", "z"]},
                            {"rel": "S", "args": ["z"]},
                            {"rel": "T", "args": ["z"]},
                        ]
                    ],
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "z"]}],
                "project": ["x"],
            },
            "closed_relations": ["S", "T"],
        }
        # T 只允许 t1，S 无 t1 -> 无自洽见证组合 -> inconsistent。
        self.assertEqual(solve(payload), {"status": "inconsistent"})
        # 给 S 补上整体见证 t1 后自洽。
        payload["facts"].append({"rel": "S", "args": ["t1"]})
        self.assertEqual(
            solve(payload), {"status": "ok", "answers": [["a"]]}
        )


class TestClosedAlternativesPartialFailure(unittest.TestCase):
    """析取方案部分失效：封闭关系无见证的方案被丢弃，其余方案仍存活。"""

    def _payload(self, closed):
        return {
            "schema": _schema_r(
                A=(1, [0], [0]),
                B=(1, [0], [0]),
                R=(2, [0, 1], [0, 1]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "B", "args": ["m"]},
            ],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "alternatives": [
                        [{"rel": "B", "args": ["x"]}],
                        [{"rel": "R", "args": ["x", "z"]}],
                    ],
                }
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "z"]}],
                "project": ["x"],
            },
            "closed_relations": closed,
        }

    def test_witnessless_alternative_is_dropped_not_fatal(self):
        # 封闭 B 只含 m：方案 B(a) 无见证被丢弃；方案 R(a,z) 开放可存活。
        self.assertEqual(
            solve(self._payload(["B"])),
            {"status": "ok", "answers": [["a"]]},
        )

    def test_all_alternatives_witnessless_is_inconsistent(self):
        # R 也封闭且无任何 R 事实 -> 两个方案都无见证 -> 无合法世界。
        self.assertEqual(
            solve(self._payload(["B", "R"])),
            {"status": "inconsistent"},
        )

    def test_open_relation_keeps_both_branches(self):
        # 不封闭：两分支都存活，R 只在其一成立 -> 无必然答案。
        self.assertEqual(
            solve(self._payload([])), {"status": "ok", "answers": []}
        )


class TestClosedEmptyFacts(unittest.TestCase):
    def test_closed_relation_with_empty_facts_is_legal_when_unused(self):
        # 空事实：没有 body 匹配，规则不触发；封闭关系外延为空合法。
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                C=(1, [1], [0]),
                R=(2, [0, 1], [0]),
            ),
            "facts": [],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                },
                {
                    "body": [{"rel": "R", "args": ["x", "y"]}],
                    "head": {"rel": "C", "args": ["y"]},
                },
            ],
            "query": {
                "body": [{"rel": "C", "args": ["y"]}],
                "project": ["y"],
            },
            "closed_relations": ["C"],
        }
        self.assertEqual(solve(payload), {"status": "ok", "answers": []})

    def test_derivation_into_empty_closed_relation_is_inconsistent(self):
        # 有 A(a) 触发规则，但封闭 C 事实为空 -> 无见证 -> inconsistent。
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                C=(1, [1], [0]),
                R=(2, [0, 1], [0]),
            ),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                },
                {
                    "body": [{"rel": "R", "args": ["x", "y"]}],
                    "head": {"rel": "C", "args": ["y"]},
                },
            ],
            "query": {
                "body": [{"rel": "C", "args": ["y"]}],
                "project": ["y"],
            },
            "closed_relations": ["C"],
        }
        self.assertEqual(solve(payload), {"status": "inconsistent"})


class TestClosedRelationsValidation(unittest.TestCase):
    """closed_relations 的非法声明定位（含零基数组下标）与兼容形态。"""

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

    def test_field_must_be_array(self):
        p = self._base()
        p["closed_relations"] = "C"
        self.assertRejects(p, "closed_relations")

    def test_empty_array_is_legal(self):
        p = self._base()
        p["closed_relations"] = []
        self.assertEqual(solve(p)["status"], "ok")

    def test_omitted_field_is_legal(self):
        self.assertEqual(solve(self._base())["status"], "ok")

    def test_unknown_relation_located_at_index(self):
        p = self._base()
        p["closed_relations"] = ["Ghost"]
        self.assertRejects(p, "closed_relations[0]")

    def test_duplicate_relation_located_at_second_index(self):
        p = self._base()
        p["closed_relations"] = ["A", "A"]
        self.assertRejects(p, "closed_relations[1]")

    def test_non_name_entries_located_at_index(self):
        for bad in (123, True, "", "关系"):
            p = self._base()
            p["closed_relations"] = [bad]
            self.assertRejects(p, "closed_relations[0]")

    def test_extra_top_level_field_still_rejected(self):
        p = self._base()
        p["unexpected"] = []
        self.assertRejects(p, "unexpected")


class TestClosedRelationsCLI(unittest.TestCase):
    """原文件入口接入 closed_relations；非法声明整次拒绝并保留旧文件。"""

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="chase-closed-")
        self.input_path = os.path.join(self.tmp, "in.json")
        self.output_path = os.path.join(self.tmp, "out.json")

    def _run_cli(self):
        proc = subprocess.run(
            [sys.executable, "-m", "chase_backend",
             self.input_path, self.output_path],
            cwd=_REPO_ROOT,
            capture_output=True,
            text=True,
        )
        return proc

    def test_closed_relation_example_runs_through_cli(self):
        payload = {
            "schema": _schema_r(
                A=(1, [0], [0]),
                C=(1, [1], [0]),
                R=(2, [0, 1], [0]),
            ),
            "facts": [
                {"rel": "A", "args": ["a"]},
                {"rel": "C", "args": ["b"]},
            ],
            "rules": [
                {
                    "body": [{"rel": "A", "args": ["x"]}],
                    "head": {"rel": "R", "args": ["x", "y"]},
                },
                {
                    "body": [{"rel": "R", "args": ["x", "y"]}],
                    "head": {"rel": "C", "args": ["y"]},
                },
            ],
            "query": {
                "body": [{"rel": "R", "args": ["x", "y"]}],
                "project": ["x", "y"],
            },
            "closed_relations": ["C"],
        }
        with open(self.input_path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False)
        proc = self._run_cli()
        self.assertEqual(proc.returncode, 0, proc.stderr)
        with open(self.output_path, encoding="utf-8") as fh:
            self.assertEqual(
                json.load(fh),
                {"status": "ok", "answers": [["a", "b"]]},
            )

    def test_invalid_closed_declaration_keeps_old_output(self):
        old_result = {"status": "ok", "answers": [["OLD"]]}
        atomic_write_json(self.output_path, old_result)
        bad = {
            "schema": _schema_r(A=(1, [0], [0])),
            "facts": [{"rel": "A", "args": ["a"]}],
            "rules": [],
            "query": {
                "body": [{"rel": "A", "args": ["x"]}],
                "project": ["x"],
            },
            "closed_relations": ["Ghost"],
        }
        with open(self.input_path, "w", encoding="utf-8") as fh:
            json.dump(bad, fh, ensure_ascii=False)
        proc = self._run_cli()
        self.assertNotEqual(proc.returncode, 0)
        err = json.loads(proc.stderr)
        self.assertTrue(
            err["path"].endswith("closed_relations[0]")
        )
        with open(self.output_path, encoding="utf-8") as fh:
            self.assertEqual(json.load(fh), old_result)


if __name__ == "__main__":
    unittest.main(verbosity=2)
