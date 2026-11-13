"""查询聚合 ``aggregate="min_count"`` 的实现。

语义
----
科研目录审核需要回答：当待确认对象的**实际身份未知**时，查询投影在某个
合法世界中至少要区分出多少个关联结果。形式化地：

1. 对每个存活 chase 分支（一个 canonical model，代表一族合法世界），按
   query body 求全部同态绑定，经 project 投影后按**实际身份**去重——
   匿名对象按并查集规范化后的代表身份计数，绑定到同一常量（或合并为
   同一等价类）的不同 Skolem 编号只算一个；
2. 合法世界可以在 canonical model 之上进一步把自由空对象识别为同一
   对象、或识别为某个输入常量；每一次识别都可能引发**新的规则匹配、
   键合并、析取方案选择与封闭关系见证**，这些后果必须全部自洽。因此
   识别后要把 chase 重新跑到不动点（复用 :func:`advance_branch` 的完整
   分裂语义），而不能只在已经生成的结果上做合并；
3. 取所有合法世界（全部存活分支及其全部自洽识别延拓）上投影基数的
   最小值。

为什么不能直接数 answers 或直接数匿名编号
------------------------------------------
* ``answers`` 只保留分量全为输入常量的元组，匿名关联结果被整体丢弃，
  必然低估（题面例中 answers 为空而 min_count 为 1）；
* chase 为不同规则触发、不同绑定各自造 Skolem 空对象，但这些对象在
  合法世界中允许相等，直接数编号必然高估；
* 反过来，识别也不是任意的：键约束可能迫使两个见证分离，封闭关系可能
  使某次识别无见证可用。枚举识别并重新 chase 才能把这些限制计入。

终止性
------
每次入栈的后继都要求投影基数严格下降（其他自洽子分支通过完成过程一并
收敛），而基数是非负整数；状态再以结构签名记忆化。rank 安全保证每个
chase 分支有限，识别只在既有对象（自由空对象根、实例中出现的常量）
之间进行，不引入新名字，故搜索空间有限且必然终止。
"""

from __future__ import annotations

from .engine import ChaseEngine, advance_branch
from .errors import InconsistentError


def _free_null_roots(branch: ChaseEngine) -> list[int]:
    """当前并查集中尚未绑定常量的空对象等价类根 id。"""
    roots = []
    for null_id in branch.uf._parent:
        root = branch.uf.find(null_id)
        if root == null_id and branch.uf._constant.get(root) is None:
            roots.append(root)
    return roots


def _instance_constants(branch: ChaseEngine) -> list[str]:
    """实例（规范化后）中出现过的全部输入常量。

    把空对象识别为常量时，只需考虑世界里已经存在的常量：引入一个全新
    常量不会帮助减少投影身份数，也不会让任何键/封闭约束更容易满足。
    """
    constants: set[str] = set()
    for tuples in branch.instance.values():
        for raw in tuples:
            for value in raw:
                canon = branch.uf.canon(value)
                if canon[0] == "c":
                    constants.add(canon[1])
    return sorted(constants)


def _canonical_signature(branch: ChaseEngine, query: dict) -> tuple:
    """分支的结构签名（与空对象命名无关），用于记忆化去重。

    包含三部分：

    * 每个等价类根绑定的常量（未绑定为 ``None``）；
    * 各关系规范化后的元组集合（空对象用基于出现结构的稳定标签表示，
      使“同构但 id 不同”的分支得到同一签名）；
    * 查询投影的规范化元组集合。
    """
    # 以规范化空对象根在全部实例元组中的首次出现顺序赋稳定标签，
    # 消除 Skolem 命名差异；常量直接用 ("c", 字符串)。
    labels: dict[int, int] = {}

    def label_for(root: int) -> int:
        if root not in labels:
            labels[root] = len(labels)
        return labels[root]

    def norm(value: tuple) -> tuple:
        canon = branch.uf.canon(value)
        if canon[0] == "c":
            return canon
        return ("n", label_for(canon[1]))

    relations = []
    for rel in sorted(branch.instance):
        tuples = sorted(
            tuple(norm(v) for v in raw)
            for raw in branch.instance[rel]
        )
        relations.append((rel, tuple(tuples)))

    bindings = tuple(sorted(
        (label_for(root), const)
        for root, const in branch.uf._constant.items()
        if const is not None
    ))
    projected = tuple(sorted(
        tuple(norm(v) for v in tpl)
        for tpl in branch.projected_tuples(query)
    ))
    return bindings, tuple(relations), projected


def _complete(branch: ChaseEngine) -> list[ChaseEngine]:
    """把一个分支（可能带未消费的分裂点）完整推进到全部自洽不动点。

    复用 :func:`advance_branch`：封闭关系多候选见证与析取方案选择都会
    正常分裂，常量冲突分支被丢弃。返回空列表表示该识别方向不存在任何
    合法世界。
    """
    finals: list[ChaseEngine] = []
    stack = [branch]
    while stack:
        status, payload = advance_branch(stack.pop())
        if status == "dead":
            continue
        if status == "final":
            finals.append(payload)
        else:
            stack.extend(payload)
    return finals


def _identifications(branch: ChaseEngine) -> list[tuple[str, Any]]:
    """枚举在当前分支上可尝试的一步身份识别。

    * 任意两个不同的自由空对象根识别为同一对象（``("nn", a, b)``）；
    * 任意自由空对象根识别为实例中的某个常量（``("nc", root, const)``）。

    已绑定常量的根之间、根与其他常量之间的识别由并查集的常量冲突检查
    兜底，无需在此枚举。
    """
    roots = _free_null_roots(branch)
    moves: list[tuple[str, Any]] = []
    for i in range(len(roots)):
        for j in range(i + 1, len(roots)):
            moves.append(("nn", roots[i], roots[j]))
    for root in roots:
        for const in _instance_constants(branch):
            moves.append(("nc", root, const))
    return moves


def _apply_identification(
    branch: ChaseEngine, move: tuple
) -> ChaseEngine | None:
    """克隆分支并施加一步识别；直接引发常量冲突时返回 None。"""
    child = branch.clone()
    kind = move[0]
    try:
        if kind == "nn":
            child.uf.union(move[1], move[2])
        else:
            child.uf.bind_constant(move[1], move[2])
    except InconsistentError:
        return None
    return child


def minimum_count(branches: list[ChaseEngine], query: dict) -> int:
    """求全部合法世界中查询投影按实际身份去重后的最小基数。

    ``branches`` 为 :func:`chase_backend.engine.chase_all` 得到的存活
    分支（至少一个，否则上层直接输出 inconsistent）。对每个分支从其
    canonical model 出发，枚举自洽的身份识别延拓，识别后重新完整
    chase，取所有可达不动点上投影基数的最小值。
    """
    best = min(len(b.projected_tuples(query)) for b in branches)
    if best == 0:
        return 0

    visited: set[tuple] = set()
    # 栈元素为已收敛的存活分支；初始分支先登记签名。
    stack: list[ChaseEngine] = []
    for branch in branches:
        sig = _canonical_signature(branch, query)
        if sig not in visited:
            visited.add(sig)
            stack.append(branch)

    while stack:
        branch = stack.pop()
        current = len(branch.projected_tuples(query))
        if current < best:
            best = current
            if best == 0:
                return 0

        for move in _identifications(branch):
            identified = _apply_identification(branch, move)
            if identified is None:
                continue  # 识别本身即要求两个不同常量相等
            for completed in _complete(identified):
                count = len(completed.projected_tuples(query))
                # 识别只会让身份更粗：基数不下降的延拓不可能再产生
                # 更优解，剪枝。
                if count >= current:
                    continue
                sig = _canonical_signature(completed, query)
                if sig in visited:
                    continue
                visited.add(sig)
                if count < best:
                    best = count
                    if best == 0:
                        return 0
                stack.append(completed)

    return best
