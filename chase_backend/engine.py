"""chase 推理引擎（确定性 head 规则 + 析取 alternatives 规则）。

语义
----
规则两种形态（恰选其一）：

* ``body -> head``：确定性规则，head 为单原子；
* ``body -> alternatives``：析取规则，alternatives 为非空方案数组，
  每个方案是非空原子数组、方案内原子须同时成立。每个 body 绑定至少
  满足一个方案（允许多个同时成立，不同绑定相互独立）。

变量与存在对象：

* body 的每个同态匹配都要求结论成立；
* 只在结论（head 或某方案）出现的变量是存在变量，表示“存在某个对象”，
  实现为 Skolem 空对象（匿名标识，不能作为查询答案）；
* 同名变量取同值：方案内未在 body 出现的同名变量共享同一存在对象；
  跨方案、跨 body 绑定的存在对象各自独立；存在对象可经键合并与其他
  对象（含常量）相等。

每个关系有键：键相同的元组所有列必须相同。键相同的元组在非键列取值
不同时触发等值合并：

* 两个空对象，或空对象与常量：用并查集合并（未知对象可相等，也可等于
  某个常量）；
* 两个不同的字符串常量：不同字符串常量永不相等，当前分支不可满足，
  抛出 :class:`InconsistentError`。

析取 chase
----------
单分支内先把确定性规则与键合并追到不动点；随后取一个尚未满足任何
方案的 ``(析取规则, body 绑定)``，按方案分裂子分支，每个子分支加入
对应方案的原子（存在变量取全新空对象）再各自收敛。导致常量冲突的
分支被丢弃——方案冲突不等于整题无解；全部分支都冲突时才不存在任何
合法世界。

每个存活分支都是一个合法世界；反过来，任意合法世界都包含某个存活
分支的同态像（沿该世界实际满足的方案逐次选择即得对应分支路径）。
因此“所有合法世界共有”的常量查询答案 = 各存活分支常量答案的交集。

终止性
------
rank 安全（逐原子沿用：共有变量目标列 rank 不低于其 body 最高位置，
存在变量目标列 rank 严格高于整个 body 的最高 rank）保证：值只会出现
在不低于其“诞生 rank”的位置，空对象只能在严格高于 body 最高 rank
的位置诞生。按 rank 归纳，每个 rank 层的对象与元组数目有限，键合并
只减少不同对象数，故每个分支在有限步内收敛。方案一旦满足便不会被
撤销（合并与新增元组只增不减匹配），每个 (规则, 绑定) 至多分裂一次，
分裂点总数有限，分支树有限，整体必然终止。
"""

from __future__ import annotations

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
    """一个 chase 分支：并查集 + 实例 + 键索引 + Skolem 缓存。"""

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
        # 同一确定性规则、同一共有变量取值只生成一组存在对象，保证可终止。
        self._skolem_cache: dict[int, dict[tuple, list[int]]] = {
            i: {} for i in range(len(rules))
        }

        for fact in facts:
            raw = tuple(("c", c) for c in fact["args"])
            self.instance[fact["rel"]].add(raw)

    # ------------------------------------------------------------------
    # 分支拷贝
    # ------------------------------------------------------------------
    def clone(self) -> "ChaseEngine":
        """深拷贝当前分支（分裂子分支用）；schema/rules 为只读共享。"""
        other = ChaseEngine.__new__(ChaseEngine)
        other.schema = self.schema
        other.rules = self.rules
        uf = UnionFind()
        uf._parent = dict(self.uf._parent)
        uf._constant = dict(self.uf._constant)
        other.uf = uf
        other._next_null = self._next_null
        other.instance = {rel: set(tpls) for rel, tpls in self.instance.items()}
        other.index = {rel: dict(idx) for rel, idx in self.index.items()}
        other._skolem_cache = {
            ri: {key: list(ids) for key, ids in cache.items()}
            for ri, cache in self._skolem_cache.items()
        }
        return other

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
            # 排序遍历：合并顺序确定，反例等输出可复现（结果语义不变）。
            for raw_tuple in sorted(self.instance[rel]):
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
    # 原子匹配
    # ------------------------------------------------------------------
    def _eval_atoms(
        self, atoms: list[dict], initial: list[dict[str, tuple]]
    ) -> list[dict[str, tuple]]:
        """以 initial 为初始部分绑定，求 atoms 的全部同态匹配延拓。"""
        matches: list[dict[str, tuple]] = [dict(b) for b in initial]
        for atom in atoms:
            rel = atom["rel"]
            args = atom["args"]
            idx = self.index[rel]
            next_matches: list[dict[str, tuple]] = []
            for binding in matches:
                # 用索引中的规范化元组做匹配，保证同值变量取值一致。
                # 排序快照取值：本轮规则触发可能向同一索引插入新键，
                # 直接迭代变化中的字典会抛 RuntimeError，新元组留待
                # 下一轮外层循环处理即可（不动点语义不变）；排序使
                # 触发顺序确定，反例等输出可复现。
                for canon_tuple in sorted(idx.values()):
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

    def _eval_body(self, body: list[dict]) -> list[dict[str, tuple]]:
        """求 body 的全部同态匹配，返回变量 -> 内部值 的映射列表。"""
        return self._eval_atoms(body, [{}])

    # ------------------------------------------------------------------
    # 确定性规则（head）
    # ------------------------------------------------------------------
    def _insert(self, rel: str, raw_tuple: tuple) -> bool:
        """插入一条原始元组并立即做键约束检查。

        返回值表示“是否发生了需要外层重建索引的变化”（新增元组或
        触发等值合并）。

        键冲突时**不**直接写入元组：合并可能改变当前索引条目的规范化
        代表值，就地写入会留下陈旧条目使后续规则看不到合并结果。
        此时只执行等值合并并返回 True，由外层循环重建索引；确定性规则
        会再次触发（Skolem 缓存保证取回同一组空对象），合并后的元组
        随重建自然进入索引（若仍有差异还会继续合并）。
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

    def _apply_deterministic(self) -> bool:
        """对所有 head 规则做一轮 chase，返回实例/等价类是否变化。"""
        changed = False
        for rule_idx, rule in enumerate(self.rules):
            head = rule.get("head")
            if head is None:
                continue
            body = rule["body"]
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
    # 析取规则（alternatives）
    # ------------------------------------------------------------------
    def _alternative_satisfied(self, alt: list[dict], binding: dict) -> bool:
        """该 body 绑定下方案是否已成立（存在延拓该绑定的方案原子匹配）。"""
        return bool(self._eval_atoms(alt, [binding]))

    def next_unsatisfied_alternative(self):
        """找一个尚未满足任何方案的 (规则序号, body 绑定)；无则返回 None。

        调用前分支须已收敛（索引与并查集一致）。满足过的绑定不会被
        撤销：键合并与新增元组只会增加匹配，不会减少。
        """
        for rule_idx, rule in enumerate(self.rules):
            alts = rule.get("alternatives")
            if alts is None:
                continue
            for binding in self._eval_body(rule["body"]):
                if not any(
                    self._alternative_satisfied(alt, binding) for alt in alts
                ):
                    return rule_idx, binding
        return None

    def apply_alternative(self, alt: list[dict], binding: dict) -> None:
        """把方案原子写入实例：body 变量取绑定值；方案内未在 body 出现
        的同名变量共享一个全新的 Skolem 空对象（跨方案、跨绑定独立）。

        直接写入 instance：键合并留给 stabilize() 的索引重建完成，
        常量冲突（若有）在子分支收敛时以 InconsistentError 暴露。
        """
        assigned: dict[str, int] = {}
        for atom in alt:
            tpl = []
            for var in atom["args"]:
                if var in binding:
                    tpl.append(binding[var])
                else:
                    if var not in assigned:
                        assigned[var] = self._new_null()
                    tpl.append(("n", assigned[var]))
            self.instance[atom["rel"]].add(tuple(tpl))

    # ------------------------------------------------------------------
    # 主循环
    # ------------------------------------------------------------------
    def stabilize(self) -> None:
        """确定性规则 + 键合并追到不动点；冲突时抛出 InconsistentError。"""
        while True:
            # 先让键合并（包括级联合并）完全收敛。
            while self._rebuild_index():
                pass
            if not self._apply_deterministic():
                break

    # ------------------------------------------------------------------
    # 查询
    # ------------------------------------------------------------------
    def answer_query(self, query: dict) -> list[tuple[str, ...]]:
        """在本分支不动点模型上求查询的常量投影答案。

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


def chase_branches(initial: ChaseEngine) -> list[ChaseEngine]:
    """从给定初始分支出发的析取 chase：返回全部自洽且收敛的分支。

    返回空列表表示不存在任何合法世界。某个方案选择导致冲突只丢弃
    对应分支，不直接判整题无解。
    """
    final: list[ChaseEngine] = []
    stack = [initial]
    while stack:
        branch = stack.pop()
        try:
            branch.stabilize()
        except InconsistentError:
            continue  # 该分支不可能对应任何合法世界
        todo = branch.next_unsatisfied_alternative()
        if todo is None:
            final.append(branch)
            continue
        rule_idx, binding = todo
        for alt in branch.rules[rule_idx]["alternatives"]:
            child = branch.clone()
            child.apply_alternative(alt, binding)
            stack.append(child)
    return final


def chase_all(schema: dict, facts: list[dict], rules: list[dict]) -> list[ChaseEngine]:
    """以输入事实为初始实例的析取 chase（见 chase_branches）。"""
    return chase_branches(ChaseEngine(schema, facts, rules))
