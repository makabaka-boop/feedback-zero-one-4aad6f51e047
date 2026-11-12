"""chase 推理引擎。

语义
----
规则形如 ``body -> head``：

* body 的每个同态匹配都要求 head 成立；
* head 中只在 head 出现的变量是存在变量，表示“存在某个对象”，
  实现为 Skolem 空对象（匿名标识，不能作为查询答案）；
* 同名变量取同值。

每个关系有键：键相同的元组所有列必须相同。当两条键相同的元组在非键列
取值不同时，触发等值合并：

* 两个空对象，或空对象与常量：用并查集合并（未知对象可相等，也可等于
  某个常量）；
* 两个不同的字符串常量：不同字符串常量永不相等，整个理论不可满足，
  抛出 :class:`InconsistentError`。

终止性
------
规则的 rank 安全性保证：值只会出现在不低于其“诞生 rank”的位置，空对象
只能在严格高于 body 最高 rank 的位置诞生。按 rank 归纳，每个 rank 层的
对象与元组数目有限，键合并只减少不同对象数，因此 chase 必然在有限步内
到达不动点，得到有限的通用（canonical）模型。该模型上取值为输入常量的
查询投影，正是所有合法世界共有的必然答案。
"""

from __future__ import annotations

from typing import Optional

from .errors import InconsistentError

# 内部表示约定：
#   常量直接用 ("c", 字符串) 表示；
#   空对象用 ("n", 整数 id) 表示。
# 元组存“原始值”，读取时经并查集规范化。


class UnionFind:
    """管理空对象合并与“空对象 -> 常量”绑定的并查集。"""

    def __init__(self) -> None:
        self._parent: dict[int, int] = {}
        # 根节点 -> 绑定的常量（同一根至多绑定一个不同常量，否则冲突）。
        self._constant: dict[int, str] = {}

    def add(self, null_id: int) -> None:
        if null_id not in self._parent:
            self._parent[null_id] = null_id

    def find(self, null_id: int) -> int:
        parent = self._parent[null_id]
        if parent != null_id:
            parent = self.find(parent)  # 路径压缩
            self._parent[null_id] = parent
        return parent

    def union(self, a: int, b: int) -> None:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return
        ca, cb = self._constant.get(ra), self._constant.get(rb)
        if ca is not None and cb is not None and ca != cb:
            raise InconsistentError(
                f"键约束要求不同常量 {ca!r} 与 {cb!r} 相等"
            )
        # 将 rb 挂到 ra 下；若 ra 无常量而 rb 有，常量随根迁移。
        self._parent[rb] = ra
        if ca is None and cb is not None:
            self._constant[ra] = cb

    def bind_constant(self, null_id: int, const: str) -> None:
        """把空对象绑定到常量；若已绑定另一个常量则不可满足。"""
        root = self.find(null_id)
        existing = self._constant.get(root)
        if existing is not None and existing != const:
            raise InconsistentError(
                f"键约束要求不同常量 {existing!r} 与 {const!r} 相等"
            )
        self._constant[root] = const

    def canon(self, value: tuple) -> tuple:
        """把一个内部值规范化为并查集代表形式。"""
        kind, payload = value
        if kind == "c":
            return value
        root = self.find(payload)
        bound = self._constant.get(root)
        if bound is not None:
            return ("c", bound)
        return ("n", root)


class ChaseEngine:
    def __init__(self, schema: dict, facts: list[dict], rules: list[dict]) -> None:
        self.schema = schema
        self.rules = rules
        self.uf = UnionFind()
        self._next_null = 0

        # rel -> set[原始元组(tuple of ("c",..)/("n",..))]
        self.instance: dict[str, set[tuple]] = {
            rel: set() for rel in schema
        }
        # rel -> {键规范化元组: 完整规范化元组}，每次重建。
        self.index: dict[str, dict[tuple, tuple]] = {
            rel: {} for rel in schema
        }
        # 规则序号 -> (共有变量绑定, Skolem 空对象 id 列表) 的缓存。
        # 同一规则、同一共有变量取值只生成一组存在对象，保证 chase 可终止。
        self._skolem_cache: dict[int, dict[tuple, list[int]]] = {
            i: {} for i in range(len(rules))
        }

        for fact in facts:
            raw = tuple(("c", c) for c in fact["args"])
            self.instance[fact["rel"]].add(raw)

    # ------------------------------------------------------------------
    # 空对象
    # ------------------------------------------------------------------
    def _new_null(self) -> int:
        null_id = self._next_null
        self._next_null += 1
        self.uf.add(null_id)
        return null_id

    # ------------------------------------------------------------------
    # 键索引与键约束
    # ------------------------------------------------------------------
    def _rebuild_index(self) -> bool:
        """按当前并查集重建键索引，执行等值合并。

        返回本次重建是否发生了新的合并（合并后需再次重建，使级联合并
        全部收敛）。
        """
        merged = False
        for rel, decl in self.schema.items():
            key_cols = decl["key"]
            idx: dict[tuple, tuple] = {}
            for raw_tuple in self.instance[rel]:
                canon = tuple(self.uf.canon(v) for v in raw_tuple)
                key = tuple(canon[c] for c in key_cols)
                existing = idx.get(key)
                if existing is None:
                    idx[key] = canon
                    continue
                if existing == canon:
                    continue
                # 键相同但完整元组不同：逐列强制相等。
                for a, b in zip(existing, canon):
                    self._force_equal(a, b)
                    merged = True
                # 合并可能改变代表值，索引留待下一轮重建。
            self.index[rel] = idx
        return merged

    def _force_equal(self, a: tuple, b: tuple) -> None:
        """键约束要求 a == b 时的等值处理。"""
        if a == b:
            return
        if a[0] == "c" and b[0] == "c":
            # 不同字符串常量永不相等。
            raise InconsistentError(
                f"键约束要求不同常量 {a[1]!r} 与 {b[1]!r} 相等"
            )
        if a[0] == "n" and b[0] == "n":
            self.uf.union(a[1], b[1])
        elif a[0] == "n":
            self.uf.bind_constant(a[1], b[1])
        else:
            self.uf.bind_constant(b[1], a[1])

    # ------------------------------------------------------------------
    # 规则求值
    # ------------------------------------------------------------------
    def _eval_body(self, body: list[dict]) -> list[dict[str, tuple]]:
        """求 body 的全部同态匹配，返回变量 -> 内部值 的映射列表。"""
        matches: list[dict[str, tuple]] = [{}]
        for atom in body:
            rel = atom["rel"]
            args = atom["args"]
            idx = self.index[rel]
            next_matches: list[dict[str, tuple]] = []
            for binding in matches:
                # 用索引中的规范化元组做匹配，保证同值变量取值一致。
                # 快照取值：本轮规则触发可能向同一索引插入新键，
                # 直接迭代变化中的字典会抛 RuntimeError，新元组留待
                # 下一轮外层循环处理即可（不动点语义不变）。
                for canon_tuple in list(idx.values()):
                    candidate = dict(binding)
                    ok = True
                    for col, var in enumerate(args):
                        val = canon_tuple[col]
                        if var in candidate:
                            if candidate[var] != val:
                                ok = False
                                break
                        else:
                            candidate[var] = val
                    if ok:
                        next_matches.append(candidate)
            matches = next_matches
            if not matches:
                break
        return matches

    def _insert(self, rel: str, raw_tuple: tuple) -> bool:
        """插入一条原始元组并立即做键约束检查。

        返回值表示“是否发生了需要外层重建索引的变化”（新增元组或
        触发等值合并）。

        键冲突时**不**直接写入元组：合并可能改变当前索引条目的规范化
        代表值，就地写入会留下陈旧条目使后续规则看不到合并结果。
        此时只执行等值合并并返回 True，由外层循环重建索引，合并后的
        元组会在重建时自然进入索引（若仍有差异还会继续合并）。
        """
        canon = tuple(self.uf.canon(v) for v in raw_tuple)
        key_cols = self.schema[rel]["key"]
        key = tuple(canon[c] for c in key_cols)
        existing = self.index[rel].get(key)
        if existing is not None:
            if existing == canon:
                return False
            for a, b in zip(existing, canon):
                self._force_equal(a, b)
            return True
        self.instance[rel].add(raw_tuple)
        self.index[rel][key] = canon
        return True

    def _apply_rules(self) -> bool:
        """对所有规则做一轮 chase，返回实例/等价类是否发生变化。"""
        changed = False
        for rule_idx, rule in enumerate(self.rules):
            body, head = rule["body"], rule["head"]
            head_rel = head["rel"]
            head_args = head["args"]
            body_vars = set()
            for atom in body:
                body_vars.update(atom["args"])
            shared = [v for v in head_args if v in body_vars]
            existential = [v for v in head_args if v not in body_vars]

            for binding in self._eval_body(body):
                # Skolem 缓存键：规则序号 + 共有变量（规范化后）取值。
                cache_key = tuple(
                    (var, self.uf.canon(binding[var])) for var in dict.fromkeys(shared)
                )
                cache = self._skolem_cache[rule_idx]
                skolem_map = cache.get(cache_key)
                if skolem_map is None:
                    skolem_ids = [self._new_null() for _ in dict.fromkeys(existential)]
                    skolem_map = list(skolem_ids)
                    cache[cache_key] = skolem_map
                null_iter = iter(skolem_map)
                assigned: dict[str, int] = {}

                head_tuple = []
                for var in head_args:
                    if var in binding:
                        head_tuple.append(binding[var])
                    else:
                        if var not in assigned:
                            assigned[var] = next(null_iter)
                        head_tuple.append(("n", assigned[var]))

                if self._insert(head_rel, tuple(head_tuple)):
                    changed = True
        return changed

    # ------------------------------------------------------------------
    # 主循环
    # ------------------------------------------------------------------
    def run(self) -> None:
        """执行 chase 直到不动点；不可满足时抛出 InconsistentError。"""
        while True:
            # 先让键合并（包括级联合并）完全收敛。
            while self._rebuild_index():
                pass
            if not self._apply_rules():
                break

    # ------------------------------------------------------------------
    # 查询
    # ------------------------------------------------------------------
    def answer_query(self, query: dict) -> list[tuple[str, ...]]:
        """在不动点模型上求必然答案。

        只保留每个分量都是输入事实常量（即规范化后为 ``("c", ...)``）
        的投影元组；匿名空对象不能作为答案。按 UTF-8 字节序排序去重。
        """
        matches = self._eval_body(query["body"])
        results: set[tuple[str, ...]] = set()
        for binding in matches:
            out: list[str] = []
            all_const = True
            for var in query["project"]:
                val = self.uf.canon(binding[var])
                if val[0] != "c":
                    all_const = False
                    break
                out.append(val[1])
            if all_const:
                results.add(tuple(out))
        return sorted(results, key=lambda t: tuple(s.encode("utf-8") for s in t))
