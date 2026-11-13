"""输入 JSON 的完整静态校验。

校验覆盖：

* schema 按关系名声明正整数 ``arity``、等长非负整数 ``ranks``、
  非空无重复的零基键列下标数组 ``key``；
* facts / rules / query 的关系引用与元数必须匹配；
* 名称为非空 ASCII 字母数字串，常量为字符串（布尔/整数等一律拒绝，
  注意 Python 中 ``bool`` 是 ``int`` 子类，整数检查必须显式排除布尔）；
* 规则结论为 ``head``（单原子）与 ``alternatives``（非空方案数组，
  每项为非空原子数组）恰选一个；
* 规则的 rank 安全性（对 head 或每个方案原子逐原子沿用）：结论共有
  变量所在列 rank 不低于该变量任一 body 位置，结论存在变量所在列
  rank 严格高于整个 body 所有位置的最高 rank。

任何一处不合法都抛出 :class:`ValidationError`，错误信息带 JSON 路径
（数组下标为零基），由上层整次拒绝、不产生新输出。
"""

from __future__ import annotations

from typing import Any

from .errors import ValidationError

# 允许出现的 ASCII 字母数字字符（名称内部使用 isascii/isalnum 判定）。
_TOP_LEVEL_KEYS = {
    "schema", "facts", "rules", "query", "closed_relations"
}
_SCHEMA_KEYS = {"arity", "ranks", "key"}
_ATOM_KEYS = {"rel", "args"}
_RULE_KEYS = {"body", "head", "alternatives"}
_QUERY_KEYS = {"body", "project"}


def _is_name(value: Any) -> bool:
    """名称：非空 ASCII 字母数字串。"""
    return (
        isinstance(value, str)
        and len(value) > 0
        and all(ch.isascii() and ch.isalnum() for ch in value)
    )


def _is_int(value: Any) -> bool:
    """整数：排除布尔（``True``/``False`` 在 Python 中也是 int）。"""
    return isinstance(value, int) and not isinstance(value, bool)


def _require_object(value: Any, path: str, what: str) -> dict:
    if not isinstance(value, dict):
        raise ValidationError(f"{what}必须是对象", path)
    return value


def _reject_extra_keys(obj: dict, allowed: set[str], path: str) -> None:
    extra = set(obj) - allowed
    if extra:
        name = sorted(extra)[0]
        raise ValidationError(f"存在不支持的字段 {name!r}", f"{path}.{name}")


def _check_atom(atom: Any, path: str, schema: dict, *, allow_vars: bool) -> None:
    """校验一个原子（事实或规则/查询中的原子）。

    ``allow_vars=False`` 时参数必须是字符串常量；``True`` 时参数必须是
    非空 ASCII 字母数字变量名。
    """
    obj = _require_object(atom, path, "原子")
    _reject_extra_keys(obj, _ATOM_KEYS, path)

    if "rel" not in obj:
        raise ValidationError("原子缺少字段 rel", f"{path}.rel")
    if "args" not in obj:
        raise ValidationError("原子缺少字段 args", f"{path}.args")

    rel = obj["rel"]
    if not _is_name(rel):
        raise ValidationError("关系名必须是非空 ASCII 字母数字串", f"{path}.rel")
    if rel not in schema:
        raise ValidationError(f"关系 {rel!r} 未在 schema 中声明", f"{path}.rel")

    args = obj["args"]
    if not isinstance(args, list):
        raise ValidationError("args 必须是数组", f"{path}.args")
    arity = schema[rel]["arity"]
    if len(args) != arity:
        raise ValidationError(
            f"关系 {rel!r} 元数为 {arity}，实参个数为 {len(args)}", f"{path}.args"
        )
    for i, arg in enumerate(args):
        arg_path = f"{path}.args[{i}]"
        if allow_vars:
            if not _is_name(arg):
                raise ValidationError(
                    "变量名必须是非空 ASCII 字母数字串", arg_path
                )
        else:
            if not isinstance(arg, str):
                raise ValidationError("事实参数必须是字符串常量", arg_path)


def _check_schema(raw_schema: Any) -> dict:
    schema_obj = _require_object(raw_schema, "$.schema", "schema")
    schema: dict[str, dict] = {}
    for rel, decl in schema_obj.items():
        path = f"$.schema.{rel}"
        if not _is_name(rel):
            raise ValidationError("关系名必须是非空 ASCII 字母数字串", path)
        decl_obj = _require_object(decl, path, "关系声明")
        _reject_extra_keys(decl_obj, _SCHEMA_KEYS, path)

        for field in ("arity", "ranks", "key"):
            if field not in decl_obj:
                raise ValidationError(f"关系声明缺少字段 {field}", f"{path}.{field}")

        arity = decl_obj["arity"]
        if not _is_int(arity) or arity <= 0:
            raise ValidationError("arity 必须是正整数", f"{path}.arity")

        ranks = decl_obj["ranks"]
        if not isinstance(ranks, list):
            raise ValidationError("ranks 必须是数组", f"{path}.ranks")
        if len(ranks) != arity:
            raise ValidationError(
                f"ranks 长度 {len(ranks)} 与 arity {arity} 不一致", f"{path}.ranks"
            )
        for i, rank in enumerate(ranks):
            if not _is_int(rank) or rank < 0:
                raise ValidationError(
                    "rank 必须是非负整数", f"{path}.ranks[{i}]"
                )

        key = decl_obj["key"]
        if not isinstance(key, list):
            raise ValidationError("key 必须是数组", f"{path}.key")
        if len(key) == 0:
            raise ValidationError("key 必须是非空数组", f"{path}.key")
        seen = set()
        for i, col in enumerate(key):
            col_path = f"{path}.key[{i}]"
            if not _is_int(col):
                raise ValidationError("键列下标必须是整数", col_path)
            if not 0 <= col < arity:
                raise ValidationError(
                    f"键列下标 {col} 超出 arity={arity} 范围", col_path
                )
            if col in seen:
                raise ValidationError("键列下标不得重复", col_path)
            seen.add(col)

        schema[rel] = {"arity": arity, "ranks": list(ranks), "key": list(key)}
    if not schema:
        raise ValidationError("schema 至少要声明一个关系", "$.schema")
    return schema


def _check_rank_safety(
    named_atoms: list[tuple[dict, str]],
    body_ranks: dict[str, list[int]],
    schema: dict,
) -> None:
    """对一组结论原子（head 单原子或某方案的全部原子）做 rank 安全检查。

    ``named_atoms`` 为 ``(原子, 原子路径)`` 对，路径用于定位错误（零基
    数组下标）。共有变量目标列 rank 不得低于该变量任一 body 位置；
    存在变量目标列 rank 必须严格高于整个 body 所有位置的最高 rank。
    """
    # body 非空且元数 >= 1，body_ranks 必然非空。
    max_body_all = max(max(v) for v in body_ranks.values())
    for atom, atom_path in named_atoms:
        ranks = schema[atom["rel"]]["ranks"]
        for col, var in enumerate(atom["args"]):
            hr = ranks[col]
            arg_path = f"{atom_path}.args[{col}]"
            if var in body_ranks:
                # 共有变量：目标列 rank 不得低于任一 body 位置。
                max_body = max(body_ranks[var])
                if hr < max_body:
                    raise ValidationError(
                        f"共有变量 {var!r} 的目标列 rank({hr}) 低于其 "
                        f"body 位置最高 rank({max_body})",
                        arg_path,
                    )
            else:
                # 存在变量：目标列 rank 必须高于整个 body 的最高 rank。
                if hr <= max_body_all:
                    raise ValidationError(
                        f"存在变量 {var!r} 的目标列 rank({hr}) 必须严格高于"
                        f"整个 body 所有位置的最高 rank({max_body_all})",
                        arg_path,
                    )


def _check_rules(raw_rules: Any, schema: dict) -> list[dict]:
    if not isinstance(raw_rules, list):
        raise ValidationError("rules 必须是数组", "$.rules")
    rules: list[dict] = []
    for ri, raw_rule in enumerate(raw_rules):
        path = f"$.rules[{ri}]"
        rule_obj = _require_object(raw_rule, path, "规则")
        _reject_extra_keys(rule_obj, _RULE_KEYS, path)
        if "body" not in rule_obj:
            raise ValidationError("规则缺少字段 body", f"{path}.body")
        has_head = "head" in rule_obj
        has_alts = "alternatives" in rule_obj
        if has_head and has_alts:
            raise ValidationError(
                "head 与 alternatives 必须恰选一个，不能同时出现",
                f"{path}.alternatives",
            )
        if not has_head and not has_alts:
            raise ValidationError(
                "规则缺少字段 head 或 alternatives（两者恰选一个）",
                f"{path}.head",
            )

        body = rule_obj["body"]
        if not isinstance(body, list) or len(body) == 0:
            raise ValidationError("规则 body 必须是非空数组", f"{path}.body")
        for bi, atom in enumerate(body):
            _check_atom(atom, f"{path}.body[{bi}]", schema, allow_vars=True)

        # 收集每个变量在 body 各位置出现的列 rank。
        body_ranks: dict[str, list[int]] = {}
        for atom in body:
            rel = atom["rel"]
            ranks = schema[rel]["ranks"]
            for col, var in enumerate(atom["args"]):
                body_ranks.setdefault(var, []).append(ranks[col])

        norm_body = [dict(a) for a in body]
        if has_head:
            head = rule_obj["head"]
            _check_atom(head, f"{path}.head", schema, allow_vars=True)
            _check_rank_safety([(head, f"{path}.head")], body_ranks, schema)
            rules.append({"body": norm_body, "head": dict(head)})
        else:
            alts = rule_obj["alternatives"]
            alts_path = f"{path}.alternatives"
            if not isinstance(alts, list) or len(alts) == 0:
                raise ValidationError("alternatives 必须是非空数组", alts_path)
            norm_alts: list[list[dict]] = []
            named: list[tuple[dict, str]] = []
            for ai, alt in enumerate(alts):
                alt_path = f"{alts_path}[{ai}]"
                if not isinstance(alt, list) or len(alt) == 0:
                    raise ValidationError("方案必须是非空原子数组", alt_path)
                for bi, atom in enumerate(alt):
                    atom_path = f"{alt_path}[{bi}]"
                    _check_atom(atom, atom_path, schema, allow_vars=True)
                    named.append((atom, atom_path))
                norm_alts.append([dict(a) for a in alt])
            _check_rank_safety(named, body_ranks, schema)
            rules.append({"body": norm_body, "alternatives": norm_alts})
    return rules


def _check_query(raw_query: Any, schema: dict) -> dict:
    path = "$.query"
    query_obj = _require_object(raw_query, path, "query")
    _reject_extra_keys(query_obj, _QUERY_KEYS, path)
    if "body" not in query_obj:
        raise ValidationError("query 缺少字段 body", f"{path}.body")
    if "project" not in query_obj:
        raise ValidationError("query 缺少字段 project", f"{path}.project")

    body = query_obj["body"]
    if not isinstance(body, list) or len(body) == 0:
        raise ValidationError("query body 必须是非空数组", f"{path}.body")
    for bi, atom in enumerate(body):
        _check_atom(atom, f"{path}.body[{bi}]", schema, allow_vars=True)

    project = query_obj["project"]
    if not isinstance(project, list) or len(project) == 0:
        raise ValidationError("project 必须是非空数组", f"{path}.project")

    body_vars: set[str] = set()
    for atom in body:
        body_vars.update(atom["args"])
    for i, var in enumerate(project):
        if not _is_name(var):
            raise ValidationError(
                "投影变量名必须是非空 ASCII 字母数字串", f"{path}.project[{i}]"
            )
        if var not in body_vars:
            raise ValidationError(
                f"投影变量 {var!r} 未在 query body 中出现", f"{path}.project[{i}]"
            )
    return {"body": [dict(a) for a in body], "project": list(project)}


def _check_closed_relations(raw: Any, schema: dict) -> list[str]:
    """校验可选的 ``closed_relations``：无重复关系名的数组，允许空数组。

    省略该字段时返回空列表（全部关系保持开放，兼容旧输入）；出现时
    必须是数组，每项为非空 ASCII 字母数字串、引用已声明的关系，且
    数组内部不得重复。任何一处非法都带 JSON 路径抛出
    :class:`ValidationError`（数组下标零基）。
    """
    if raw is None:
        return []
    path = "$.closed_relations"
    if not isinstance(raw, list):
        raise ValidationError("closed_relations 必须是数组", path)
    closed: list[str] = []
    seen: set[str] = set()
    for i, name in enumerate(raw):
        item_path = f"{path}[{i}]"
        if not _is_name(name):
            raise ValidationError(
                "封闭关系名必须是非空 ASCII 字母数字串", item_path
            )
        if name not in schema:
            raise ValidationError(
                f"关系 {name!r} 未在 schema 中声明", item_path
            )
        if name in seen:
            raise ValidationError(
                f"封闭关系 {name!r} 重复声明", item_path
            )
        seen.add(name)
        closed.append(name)
    return closed


def validate(payload: Any) -> dict:
    """校验完整输入，返回规范化后的内部结构。"""
    root = _require_object(payload, "$", "输入")
    _reject_extra_keys(root, _TOP_LEVEL_KEYS, "$")
    for field in ("schema", "facts", "rules", "query"):
        if field not in root:
            raise ValidationError(f"输入缺少顶层字段 {field}", f"$.{field}")

    schema = _check_schema(root["schema"])
    # closed_relations 引用 schema 中的关系，须在 schema 之后、facts 之前校验。
    closed_relations = _check_closed_relations(
        root.get("closed_relations"), schema
    )

    raw_facts = root["facts"]
    if not isinstance(raw_facts, list):
        raise ValidationError("facts 必须是数组", "$.facts")
    facts: list[dict] = []
    for fi, raw_fact in enumerate(raw_facts):
        _check_atom(raw_fact, f"$.facts[{fi}]", schema, allow_vars=False)
        facts.append({"rel": raw_fact["rel"], "args": list(raw_fact["args"])})

    rules = _check_rules(root["rules"], schema)
    query = _check_query(root["query"], schema)

    return {
        "schema": schema,
        "facts": facts,
        "rules": rules,
        "query": query,
        "closed_relations": closed_relations,
    }
