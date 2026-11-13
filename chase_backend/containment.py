"""compare_query 的全合法世界包含性检查。

语义
----
``contained`` 当且仅当：在**每个**包含输入事实、满足全部规则与键约束
的合法世界 W 中，旧查询（``query``）的结果都包含于新查询
（``compare_query``）的结果。两个查询的变量各自独立绑定，按投影位置
比较；结果元组允许出现匿名对象（与 ``answers`` 只保留常量元组不同）。
合法世界可以任意增添对象与事实、允许无限，因此**不能仅比当前答案**。

判定方法（冻结 + 分模式 chase）
------------------------------
旧查询 body 在合法世界 W 中的一个匹配 h 把每个变量映到 W 的对象：某个
输入常量或某个匿名对象。按“哪些变量映到同一常量 / 同一匿名对象”把
匹配分成有限多种等值模式：每个变量或取某个输入常量，或取某个匿名块
（块内同值、块间互异且异于所有常量）。对每种模式 ρ，把旧查询 body
冻结成事实（常量照常、匿名块取全新空对象）加入输入事实得到 J_ρ：

* 若 chase(J_ρ) 没有存活分支，说明不存在包含该模式匹配的合法世界，
  该模式不产生反例；
* 否则每个存活分支都是包含 J_ρ 的有限合法世界。若某分支中冻结投影
  元组 t 不命中新查询，该分支本身就是一个有限反例；
* 若某模式所有存活分支都令 t 命中新查询，由 chase 的通用性（任意
  包含 J_ρ 的合法世界都包含某存活分支保持 J_ρ 对象的同态像）可知
  所有包含该模式匹配的合法世界都令 t 命中新查询。

所有模式都通过时 ``contained=True``；否则取首个违例分支构造有限反例
``{"objects", "facts", "tuple"}``：

* ``objects``：非空 ASCII 字母数字对象名 -> 常量字符串或 ``None``
  （匿名）；各名表示不同对象，非 null 值唯一且覆盖全部输入常量；
* ``facts``：分支收敛后的规范化事实（沿用原子结构，args 引用对象名），
  满足全部声明（包含输入事实、键约束、全部规则）；
* ``tuple``：命中旧查询而不命中新查询的投影元组（引用对象名）。
"""

from __future__ import annotations

from .engine import ChaseEngine, chase_branches


def _input_constants(facts: list[dict]) -> list[str]:
    """输入事实中出现的全部常量（按 UTF-8 字节序排列，保证确定性）。"""
    consts = {c for fact in facts for c in fact["args"]}
    return sorted(consts, key=lambda s: s.encode("utf-8"))


def _iter_patterns(variables: list[str], constants: list[str]) -> list[dict]:
    """枚举旧查询变量的等值/常量模式。

    每个变量或绑定到某个输入常量，或绑定到某个匿名块（同块同值、
    异块互异且异于所有常量）。返回 ``dict[var, ("c", 常量) |
    ("n", 块号)]`` 的列表，块号按变量首次出现从 0 编号。
    """
    patterns: list[dict] = [{}]
    for var in variables:
        extended: list[dict] = []
        for pattern in patterns:
            blocks = sorted(
                payload
                for kind, payload in pattern.values()
                if kind == "n"
            )
            for const in constants:
                extended.append({**pattern, var: ("c", const)})
            for block in blocks:
                extended.append({**pattern, var: ("n", block)})
            # 新匿名块：块号为现有块数（块号始终是 0..k-1）。
            extended.append({**pattern, var: ("n", len(blocks))})
        patterns = extended
    return patterns


def _hits(branch: ChaseEngine, query: dict, target: tuple) -> bool:
    """分支中是否存在投影恰好等于 target 的查询匹配（分量均为规范化值）。"""
    for binding in branch._eval_body(query["body"]):
        projection = tuple(
            branch.uf.canon(binding[var]) for var in query["project"]
        )
        if projection == target:
            return True
    return False


def _build_counterexample(
    branch: ChaseEngine, schema: dict, target: tuple
) -> dict:
    """把违例分支整理成有限反例：对象命名 + 规范化事实 + 投影元组。

    分支已收敛，其规范化实例满足键约束与全部规则，且包含输入事实；
    冻结投影元组 target 命中旧查询而不命中新查询。
    """
    canon_facts: list[tuple[str, tuple]] = []
    seen: set[tuple[str, tuple]] = set()
    for rel in schema:
        for raw in sorted(branch.instance[rel]):
            canon = tuple(branch.uf.canon(v) for v in raw)
            if (rel, canon) not in seen:
                seen.add((rel, canon))
                canon_facts.append((rel, canon))

    values: set[tuple] = set()
    for _, canon in canon_facts:
        values.update(canon)
    values.update(target)
    # 确定性排序：常量（"c"）在前按 UTF-8，匿名对象（"n"）在后按 id。
    ordered = sorted(values)
    names = {value: f"o{i}" for i, value in enumerate(ordered)}
    objects = {
        names[value]: (value[1] if value[0] == "c" else None)
        for value in ordered
    }
    facts = [
        {"rel": rel, "args": [names[v] for v in canon]}
        for rel, canon in canon_facts
    ]
    return {
        "objects": objects,
        "facts": facts,
        "tuple": [names[v] for v in target],
    }


def _check_pattern(
    schema: dict,
    facts: list[dict],
    rules: list[dict],
    query: dict,
    compare_query: dict,
    pattern: dict,
) -> dict | None:
    """检查一种等值/常量模式；某存活分支遗漏冻结投影元组时返回反例。"""
    engine = ChaseEngine(schema, facts, rules)
    # 冻结旧查询 body：常量照常，匿名块取全新 Skolem 空对象。
    block_nulls: dict[int, int] = {}
    frozen: dict[str, tuple] = {}
    for atom in query["body"]:
        raw = []
        for var in atom["args"]:
            kind, payload = pattern[var]
            if kind == "c":
                value = ("c", payload)
            else:
                null_id = block_nulls.get(payload)
                if null_id is None:
                    null_id = engine._new_null()
                    block_nulls[payload] = null_id
                value = ("n", null_id)
            frozen[var] = value
            raw.append(value)
        engine.instance[atom["rel"]].add(tuple(raw))

    for branch in chase_branches(engine):
        target = tuple(
            branch.uf.canon(frozen[var]) for var in query["project"]
        )
        if not _hits(branch, compare_query, target):
            return _build_counterexample(branch, schema, target)
    return None


def check_containment(
    schema: dict,
    facts: list[dict],
    rules: list[dict],
    query: dict,
    compare_query: dict,
) -> tuple[bool, dict | None]:
    """判断在每个合法世界中旧查询结果是否都包含于新查询结果。

    返回 ``(contained, counterexample)``：成立时 counterexample 为
    ``None``；否则为任一有限反例。调用前须保证输入一致（至少存在
    一个合法世界）。
    """
    constants = _input_constants(facts)
    variables: list[str] = []
    seen: set[str] = set()
    for atom in query["body"]:
        for var in atom["args"]:
            if var not in seen:
                seen.add(var)
                variables.append(var)

    for pattern in _iter_patterns(variables, constants):
        counterexample = _check_pattern(
            schema, facts, rules, query, compare_query, pattern
        )
        if counterexample is not None:
            return False, counterexample
    return True, None
