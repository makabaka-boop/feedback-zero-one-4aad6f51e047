"""chase 推理引擎（确定性 head 规则 + 析取 alternatives 规则 + 封闭关系）。

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

封闭关系（closed_relations）
----------------------------
声明为封闭的关系，其在任何合法世界中的外延必须**恰等于**输入 facts
中该关系去重后的元组集合（其余关系仍可自由扩充）：

* 初始化时输入事实即封闭关系的全部内容，天然满足；
* 规则向封闭关系推导出的每条元组都必须能**整体**对应某条输入事实
  元组：常量列逐列相等；匿名列（存在对象）在匹配中绑定到对应事实列
  的常量——禁止逐列拼接，即不能把不同事实行的列拼成一条匹配；
* 同一对象在全部位置取值一致：不同匹配对同一匿名对象的绑定经并查集
  统一，绑定到不同常量即触发常量冲突；
* 没有任何可匹配的事实行 -> 当前分支不可满足；恰有一个候选 -> 匿名
  对象绑定常量后推导元组与事实行重合，不写入新元组；多个候选 -> 按
  候选分裂子分支（与析取方案共用同一套分支栈）。

析取 chase
----------
单分支内先把确定性规则与键合并追到不动点；封闭关系的多候选匹配与
尚未满足任何方案的 ``(析取规则, body 绑定)`` 都表现为分裂点：前者按
候选事实行分裂，后者按方案分裂。导致常量冲突的分支被丢弃——单个
选择冲突不等于整题无解；全部分支都冲突时才不存在任何合法世界。

每个存活分支都是一个合法世界；反过来，任意合法世界都包含某个存活
分支的同态像（沿该世界实际满足的方案与封闭关系见证逐次选择即得对应
分支路径）。因此“所有合法世界共有”的常量查询答案 = 各存活分支常量
答案的交集。

终止性
------
rank 安全（逐原子沿用：共有变量目标列 rank 不低于其 body 最高位置，
存在变量目标列 rank 严格高于整个 body 的最高 rank）保证：值只会出现
在不低于其“诞生 rank”的位置，空对象只能在严格高于 body 最高 rank
的位置诞生。按 rank 归纳，每个 rank 层的对象与元组数目有限，键合并
只减少不同对象数，故每个分支在有限步内收敛。方案一旦满足便不会被
撤销（合并与新增元组只增不减匹配）；封闭关系只绑定匿名对象、不新增
元组，每个 (规则, 绑定) 至多分裂一次，分裂点总数有限，分支树有限，
整体必然终止。
"""

from __future__ import annotations

from typing import Any

from .errors import InconsistentError

# 内部表示约定：
#   常量直接用 ("c", 字符串) 表示；
#   空对象用 ("n", 整数 id) 表示。
# 元组存“原始值”，读取时经并查集规范化。


class _Suspended(Exception):
    """内部信号：封闭关系出现多候选见证，需把分支交还外层分裂。

    携带挂起信息 ``(rel, raw_tuple, 候选事实行列表)``；由
    :func:`chase_all` 捕获后按候选生成子分支。不对外暴露。
    """


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

    def __init__(
        self,
        schema: dict,
        facts: list[dict],
        rules: list[dict],
        closed_relations: list[str] | None = None,
    ) -> None:
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

        # 封闭关系：名称集合，以及每个封闭关系的输入事实元组集合
        # （全部由常量构成，已按集合去重）。封闭关系不允许出现这些
        # 元组之外的任何元组。
        self.closed: set[str] = set(closed_relations or ())
        self.closed_facts: dict[str, set[tuple]] = {
            rel: set() for rel in self.closed
        }
        # 挂起的封闭关系多候选见证：
        # (rel, 原始推导元组, 候选事实行(常量元组) 列表)，由外层分裂消费。
        self.pending = None

        for fact in facts:
            raw = tuple(("c", c) for c in fact["args"])
            self.instance[fact["rel"]].add(raw)
            if fact["rel"] in self.closed:
                self.closed_facts[fact["rel"]].add(raw)

    # ------------------------------------------------------------------
    # 分支拷贝
    # ------------------------------------------------------------------
    def clone(self) -> "ChaseEngine":
        """深拷贝当前分支（分裂子分支用）；schema/rules/封闭集为只读共享。"""
        other = ChaseEngine.__new__(ChaseEngine)
        other.schema = self.schema
        other.rules = self.rules
        uf = UnionFind()
        uf._parent = dict(self.uf._parent)
        uf._constant = dict(self.uf._constant)
        # 克隆后可能对从未参与合并的空对象直接做 canon/find（封闭关系
        # 见证绑定会用到），确保 0.._next_null 内每个 id 都有 parent 条目。
        for null_id in range(self._next_null):
            uf._parent.setdefault(null_id, null_id)
        other.uf = uf
        other._next_null = self._next_null
        other.instance = {rel: set(tpls) for rel, tpls in self.instance.items()}
        other.index = {rel: dict(idx) for rel, idx in self.index.items()}
        other._skolem_cache = {
            ri: {key: list(ids) for key, ids in cache.items()}
            for ri, cache in self._skolem_cache.items()
        }
        # 只读结构直接共享；子分支从新分裂点开始，不继承挂起状态。
        other.closed = self.closed
        other.closed_facts = self.closed_facts
        other.pending = None
        return other

    def _remap_nulls_fresh(self, null_ids: set[int]) -> dict[int, int]:
        """把给定空对象在本分支内替换为全新空对象，返回旧 id -> 新 id。

        封闭关系多候选分裂时，让每个子分支对挂起元组中的存在对象持有
        **私有的、互不相同的 id**：克隆本身已隔离并查集，相同 id 不会
        造成跨分支误判，但私有名可彻底避免跨分支的对象别名，使各分支
        的存在对象身份显式独立、便于推理与排障。重写需同步覆盖并查集、
        实例原始元组与 Skolem 缓存（含缓存键内嵌的空对象元组）；键索引
        留待 stabilize() 重建。
        """
        if not null_ids:
            return {}
        mapping = {nid: self._new_null() for nid in null_ids}

        def remap_value(value: tuple) -> tuple:
            if value[0] == "n" and value[1] in mapping:
                return ("n", mapping[value[1]])
            return value

        # 并查集：新 id 已由 _new_null 建为独立根，迁移旧根的常量绑定。
        old_roots = {self.uf.find(nid) for nid in null_ids}
        for old, new in mapping.items():
            root = self.uf.find(old)
            const = self.uf._constant.get(root)
            if const is not None and root in old_roots:
                self.uf._constant.setdefault(new, const)
        for root in old_roots:
            self.uf._constant.pop(root, None)
        for old in null_ids:
            self.uf._parent.pop(old, None)
        # 剔除仍指向已删除 id 的悬挂父指针（等价类已整体迁移）。
        for nid, parent in list(self.uf._parent.items()):
            if parent in null_ids and nid not in null_ids:
                self.uf._parent[nid] = nid
        # 实例中的原始元组同步替换。
        for rel, tuples in self.instance.items():
            rebuilt = set()
            for raw in tuples:
                rebuilt.add(tuple(remap_value(v) for v in raw))
            self.instance[rel] = rebuilt
        # Skolem 缓存中的 id 列表与缓存键（键内可能嵌着空对象的规范化
        # 元组）都要同步替换，否则重跑规则会因键失配而另造新对象，
        # 破坏“同一绑定同一组存在对象”的分支内缓存语义。
        for cache in self._skolem_cache.values():
            for key, ids in list(cache.items()):
                new_key = tuple(
                    (var, remap_value(val)) for var, val in key
                )
                cache[new_key] = [mapping.get(nid, nid) for nid in ids]
                if new_key != key:
                    del cache[key]
        # 索引含旧 id 的规范化条目，整体作废，由下一轮重建恢复。
        for rel in self.index:
            self.index[rel] = {}
        return mapping

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

    def _eval_body(self, body: list[dict]) -> list[dict[str, tuple]]:
        """求 body 的全部同态匹配，返回变量 -> 内部值 的映射列表。"""
        return self._eval_atoms(body, [{}])

    # ------------------------------------------------------------------
    # 确定性规则（head）
    # ------------------------------------------------------------------
    def _closed_candidates(
        self, rel: str, raw_tuple: tuple
    ) -> list[tuple]:
        """求封闭关系推导元组可整体对应的全部输入事实行（见证候选）。

        匹配按**整条元组**进行，禁止逐列拼接：对每条输入事实行，常量列
        必须与推导元组规范化值逐列相等；推导元组中的匿名对象在该行下
        被要求等于对应事实列常量。同一匿名对象在本行多次出现时，各列
        必须指向同一常量，否则该行不是候选。

        候选之间的匿名绑定冲突（同一对象被不同候选要求等于不同常量）
        在分支选定见证后由并查集的 ``bind_constant`` 暴露为常量冲突。
        """
        canon = tuple(self.uf.canon(v) for v in raw_tuple)
        candidates: list[tuple] = []
        for fact_tuple in self.closed_facts[rel]:
            null_to_const: dict[int, str] = {}
            feasible = True
            for derived, fact_val in zip(canon, fact_tuple):
                const = fact_val[1]  # 事实行全部是 ("c", 字符串)
                if derived[0] == "c":
                    if derived[1] != const:
                        feasible = False
                        break
                else:
                    # 匿名对象：本行内多次出现必须指向同一个常量。
                    bound = null_to_const.setdefault(derived[1], const)
                    if bound != const:
                        feasible = False
                        break
            if feasible:
                candidates.append(fact_tuple)
        return candidates

    def _bind_closed_witness(
        self, raw_tuple: tuple, fact_tuple: tuple
    ) -> None:
        """选定一条见证事实行：把推导元组中的匿名对象绑定到对应常量。"""
        canon = tuple(self.uf.canon(v) for v in raw_tuple)
        for derived, fact_val in zip(canon, fact_tuple):
            if derived[0] == "n":
                self.uf.bind_constant(derived[1], fact_val[1])

    def _insert_closed(self, rel: str, raw_tuple: tuple) -> bool:
        """向封闭关系写入推导元组。

        封闭关系的外延被钉死为输入事实集合，因此推导元组不能真正新增：

        * 无候选事实行 -> 违反封闭性，当前分支不可满足；
        * 唯一候选 -> 匿名对象绑定对应常量，元组与事实行重合（不写入）；
        * 多个候选 -> 抛出 :class:`_Suspended`，由外层按候选分裂。

        返回值与 :meth:`_insert` 对齐：唯一候选且发生了新绑定时为 True，
        纯常量重合（无变化）为 False。
        """
        candidates = self._closed_candidates(rel, raw_tuple)
        if not candidates:
            raise InconsistentError(
                f"封闭关系 {rel!r} 出现了输入事实之外的元组"
            )
        if len(candidates) > 1:
            self.pending = (rel, raw_tuple, candidates)
            raise _Suspended(rel)
        # 唯一候选：绑定前记录哪些匿名列尚未落到常量，绑定后据此判断
        # 实例是否发生了需要外层重建索引的变化。
        canon = tuple(self.uf.canon(v) for v in raw_tuple)
        unbound = {
            v[1] for v in canon
            if v[0] == "n"
            and self.uf._constant.get(self.uf.find(v[1])) is None
        }
        self._bind_closed_witness(raw_tuple, candidates[0])
        newly_bound = any(
            self.uf._constant.get(self.uf.find(nid)) is not None
            for nid in unbound
        )
        return newly_bound

    def _insert(self, rel: str, raw_tuple: tuple) -> bool:
        """插入一条原始元组并立即做键约束/封闭关系检查。

        封闭关系走 :meth:`_insert_closed`（多候选时抛 :class:`_Suspended`
        交外层分裂）；开放关系走原来的键约束逻辑。

        返回值表示“是否发生了需要外层重建索引的变化”（新增元组或
        触发等值合并）。

        键冲突时**不**直接写入元组：合并可能改变当前索引条目的规范化
        代表值，就地写入会留下陈旧条目使后续规则看不到合并结果。
        此时只执行等值合并并返回 True，由外层循环重建索引；确定性规则
        会再次触发（Skolem 缓存保证取回同一组空对象），合并后的元组
        随重建自然进入索引（若仍有差异还会继续合并）。
        """
        if rel in self.closed:
            return self._insert_closed(rel, raw_tuple)
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

    def expand_alternative(
        self, alt: list[dict], binding: dict
    ) -> list["ChaseEngine"]:
        """一次性展开一个方案，返回全部自洽的子分支（可能为空）。

        方案内未在 body 出现的同名变量共享同一组全新 Skolem 空对象
        （跨方案、跨绑定各自独立）。随后按原子关系类型分流：

        * 开放关系原子：元组直接写入实例，键合并留给子分支 stabilize()；
        * 封闭关系原子：不允许新增元组，改求可整体对应的输入事实行，
          按候选分裂（同一方案多个封闭原子取候选的笛卡尔积）；无候选
          的组合直接丢弃，不产生分支。

        一次性展开保证每个 ``(析取规则, body 绑定)`` 至多分裂一次，
        不会因封闭原子多候选而重复造空对象；封闭绑定引发的常量冲突
        在 :meth:`UnionFind.bind_constant` 处就地暴露，对应组合被丢弃。
        """
        # 1) 用同一组空对象把方案所有原子物化为原始元组。
        assigned: dict[str, int] = {}
        materialized: list[tuple[str, tuple]] = []
        for atom in alt:
            tpl = []
            for var in atom["args"]:
                if var in binding:
                    tpl.append(binding[var])
                else:
                    if var not in assigned:
                        assigned[var] = self._new_null()
                    tpl.append(("n", assigned[var]))
            materialized.append((atom["rel"], tuple(tpl)))

        # 2) 基础子分支：只写入开放关系原子。
        base = self.clone()
        for rel, raw_tuple in materialized:
            if rel not in self.closed:
                base.instance[rel].add(raw_tuple)

        # 3) 封闭原子逐个按见证候选做笛卡尔积扩展。
        children: list[ChaseEngine] = [base]
        for rel, raw_tuple in materialized:
            if rel not in self.closed:
                continue
            next_children: list[ChaseEngine] = []
            for child in children:
                candidates = child._closed_candidates(rel, raw_tuple)
                for fact_tuple in candidates:
                    grand = child.clone()
                    try:
                        grand._bind_closed_witness(raw_tuple, fact_tuple)
                    except InconsistentError:
                        continue  # 该候选要求同一对象等于两个不同常量
                    next_children.append(grand)
            children = next_children
            if not children:
                break
        return children

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
        results = self.projected_tuples(query)
        constant_only = {
            t for t in results if all(kind == "c" for kind, _ in t)
        }
        return sorted(
            (tuple(payload for _, payload in t) for t in constant_only),
            key=lambda t: tuple(s.encode("utf-8") for s in t),
        )

    def projected_tuples(self, query: dict) -> set[tuple]:
        """求查询绑定经 project 投影、按**实际身份**去重后的元组集合。

        与 :meth:`answer_query` 不同，匿名空对象同样计数：每个投影分量
        先经并查集规范化，空对象按其规范化代表（``("n", 根 id)``）比较，
        常量按 ``("c", 字符串)`` 比较。绑定到同一常量（或合并为同一
        等价类）的不同匿名编号在此只算一个身份——计数必须基于规范化
        身份，不能直接数 chase 生成的匿名编号，也不能数只含常量的
        answers。
        """
        matches = self._eval_body(query["body"])
        results: set[tuple] = set()
        for binding in matches:
            results.add(
                tuple(self.uf.canon(binding[var]) for var in query["project"])
            )
        return results


def advance_branch(branch: ChaseEngine) -> tuple[str, Any]:
    """把一个 chase 分支向前推进**一步**。

    返回 ``(状态, 载荷)``：

    * ``("dead", None)``：分支触发常量冲突，不可能对应任何合法世界；
    * ``("final", branch)``：已收敛且不存在未满足的析取绑定，本分支
      即一个合法世界（canonical model）；
    * ``("split", children)``：分支在一个分裂点上展开为若干自洽子分支
      （封闭关系多候选见证，或析取规则的方案展开），交由外层入栈。

    抽成独立函数是为了让“先强制识别两个对象、再把 chase 跑到不动点”
    的聚合计算复用同一套收敛/分裂语义，而不是只在已生成结果上做合并。
    """
    # 优先消费挂起的封闭关系多候选：每个候选一个子分支。挂起元组
    # 中的存在对象在**每个子分支内**替换为该分支私有的新空对象
    # （并查集、实例元组、Skolem 缓存键与值同步重映射），使各候选
    # 的见证身份显式独立；随后绑定该候选见证，常量冲突即丢弃该
    # 子分支。
    if branch.pending is not None:
        rel, raw_tuple, candidates = branch.pending
        branch.pending = None
        suspended_nulls = [v[1] for v in raw_tuple if v[0] == "n"]
        children: list[ChaseEngine] = []
        for fact_tuple in candidates:
            child = branch.clone()
            id_map = child._remap_nulls_fresh(set(suspended_nulls))
            child_tuple = tuple(
                ("n", id_map[v[1]]) if v[0] == "n" else v
                for v in raw_tuple
            )
            try:
                child._bind_closed_witness(child_tuple, fact_tuple)
            except InconsistentError:
                continue
            children.append(child)
        return "split", children

    try:
        branch.stabilize()
    except InconsistentError:
        # 该分支不可能对应任何合法世界。
        return "dead", None
    except _Suspended:
        # 确定性规则触发封闭关系多候选：同分支带着挂起信息再走一步，
        # 下一轮按候选分裂（已完成的合并/元组变化都保留在分支上）。
        return "split", [branch]

    todo = branch.next_unsatisfied_alternative()
    if todo is None:
        return "final", branch
    rule_idx, binding = todo
    children = []
    for alt in branch.rules[rule_idx]["alternatives"]:
        # 每个方案一次性展开：开放原子写入 + 封闭原子见证组合；
        # 无自洽见证组合时返回空列表，该方案对当前绑定整体失效。
        children.extend(branch.expand_alternative(alt, binding))
    return "split", children


def chase_all(
    schema: dict,
    facts: list[dict],
    rules: list[dict],
    closed_relations: list[str] | None = None,
) -> list[ChaseEngine]:
    """析取 chase：返回全部自洽且收敛的分支（每个都是一个合法世界）。

    返回空列表表示不存在任何合法世界。分裂点有两类：

    * 析取规则的未满足 ``(规则, 绑定)``：按方案数分裂；
    * 封闭关系的多候选见证：按可匹配的输入事实行分裂。

    单个选择导致常量冲突只丢弃对应分支，不直接判整题无解；所有分支
    都冲突时返回空列表，由上层输出 ``inconsistent``。
    """
    final: list[ChaseEngine] = []
    stack = [ChaseEngine(schema, facts, rules, closed_relations)]
    while stack:
        status, payload = advance_branch(stack.pop())
        if status == "dead":
            continue
        if status == "final":
            final.append(payload)
        else:
            stack.extend(payload)
    return final
