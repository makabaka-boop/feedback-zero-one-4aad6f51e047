# 后端交换作业：带键约束的存在规则 chase 推理后端

从零实现的 Python（仅标准库）后端：接收包含 `schema` / `facts` / `rules` /
`query` 的 JSON，在**所有合法世界共有**的语义下计算查询的必然答案
（certain answers）。

## 目录结构

```
.
├── chase_backend/            # 源码包
│   ├── __init__.py           # 对外 API：solve / 异常类型
│   ├── __main__.py           # 命令行入口 python -m chase_backend
│   ├── validator.py          # 完整输入校验（错误带 JSON 字段路径）
│   ├── engine.py             # chase 引擎：并查集 + Skolem 空对象 + 键合并
│   ├── solver.py             # 校验 -> chase -> 查询 的编排
│   ├── io_utils.py           # 原子写入（临时文件 + os.replace）
│   └── errors.py             # ValidationError / InconsistentError
├── tests/
│   └── test_acceptance.py    # 独立验收（35 项，仅依赖 unittest）
├── examples/
│   ├── spec_example.json            # 题面示例输入
│   └── spec_example.expected.json   # 期望输出
└── README.md
```

## 输入 / 输出契约

### 输入 JSON

```json
{
  "schema": {
    "Rel": {"arity": 2, "ranks": [0, 1], "key": [0]}
  },
  "facts": [{"rel": "Rel", "args": ["常量1", "常量2"]}],
  "rules": [
    {
      "body": [{"rel": "Rel", "args": ["x", "y"]}],
      "head": {"rel": "Out", "args": ["x", "z"]}
    }
  ],
  "query": {
    "body": [{"rel": "Out", "args": ["x", "z"]}],
    "project": ["x", "z"]
  }
}
```

* **schema**：按关系名声明
  * `arity`：正整数（整数禁布尔，`true/false` 一律拒绝）；
  * `ranks`：与 `arity` 等长的非负整数数组；
  * `key`：非空、无重复、取值在零基 `[0, arity)` 内的键列下标数组。
* **facts**：`rel` + `args`，参数为 Unicode 字符串常量，按集合解释
  （重复事实自动去重）。空事实数组合法。
* **rules**：非空 `body` 与单个 `head`，原子参数全部是变量（非空
  ASCII 字母数字串）。
  * 每个 body 匹配都必须有 head 成立；
  * 只在 head 出现的变量是存在变量（存在某个对象，实现为匿名 Skolem
    对象）；同名变量取同值；
  * **rank 安全**：head 共有变量所在列的 rank 不得低于该变量任一
    body 位置的 rank；head 存在变量所在列的 rank 必须严格高于
    全部 body 位置的最高 rank。
* **query**：非空 `body` 与非空 `project`，投影变量必须在 body 出现。
* 关系引用与元数必须匹配；名称限非空 ASCII 字母数字串，常量为
  Unicode 字符串。

### 合法世界与不可满足

合法世界可以增加对象与事实（允许无限），但必须：包含全部输入事实、
满足全部规则、每个关系中键相同的元组在所有列上取值相同。不同字符串
常量永不相等；未知对象之间、未知对象与常量之间可以相等。不存在任何
合法世界时输出：

```json
{"status": "inconsistent"}
```

### 输出 JSON

* `{"status": "ok", "answers": [[...], ...]}`：只包含各分量都是
  **输入事实常量**的投影元组（匿名标识不能作为答案），去重后按
  **UTF-8 元组字典序**（逐分量比较 UTF-8 字节序列）排序。
* `{"status": "inconsistent"}`：无合法世界。

## 语义与算法

### 为什么“只按现有事实连接”会漏答案

题面示例：规则 `A(x) -> R(x,y)` 会生成 `R(a, 匿名对象)`，规则
`B(x,z) -> R(x,z)` 生成 `R(a,b)`。`R` 以首列为键，两行键相同，因此
匿名对象必须等于常量 `b`，查询两列的必然答案就是 `(a,b)`。若只在
输入事实上做连接，第一条规则推出的信息就丢了。

### Chase（追赶）流程

1. 以输入事实初始化实例（常量用 `("c", s)`、匿名对象用 `("n", id)`
   内部表示）。
2. **规则触发**：求 body 的全部同态匹配；共有变量直接取值，存在变量
   取 Skolem 空对象。同一规则、同一共有变量取值只生成一组 Skolem
   对象（缓存），避免重复造对象。
3. **键约束合并**：键相同的两行在非键列取值不同时，用**并查集**强制
   等值——空对象之间合并、空对象绑定常量；若要求两个不同字符串常量
   相等，则立即判定 `inconsistent`。合并后重建索引，处理级联。
4. 重复 2–3 直到不动点。

### 终止性（rank 归纳）

rank 安全条件保证：值只会出现在不低于其“诞生 rank”的位置，空对象
只能在严格高于 body 最高 rank 的位置诞生。按 rank 归纳，rank 0 只有
有限个输入常量；假设低于 rank r 的对象有限，则 rank r 处能诞生的
Skolem 对象由低 rank 的有限取值决定，也是有限的；键合并只会减少不同
对象数。因此 chase 必然在有限步终止，得到有限的通用模型
（canonical model），其上的常量投影即所有合法世界共有的必然答案。

### 查询求值

在不动点模型上对 query body 做同态求值，保留每个投影分量规范化后
都是常量的元组，去重并按 UTF-8 字节序排序。

## 使用方式

### 命令行（入口）

```bash
python -m chase_backend examples/spec_example.json /tmp/out.json
cat /tmp/out.json
```

* 成功（含 `inconsistent` 这一正常结果）：退出码 0，输出文件被
  **原子替换**（先写同目录临时文件，`fsync` 后 `os.replace`）。
* 输入文件缺失、JSON 非法或字段校验失败：退出码非 0，错误以
  `{"error": ..., "path": "JSON路径"}` 打到 stderr，**不创建、不覆盖
  输出文件，旧结果完整保留**。

### Python API

```python
from chase_backend import solve
from chase_backend.errors import ValidationError

try:
    result = solve(payload)   # payload 为已 json.load 的 dict
except ValidationError as exc:
    exc.path     # 例如 "rules[0].head.args[1]"
    exc.message
```

## 独立验收

```bash
python -I tests/test_acceptance.py
# 或
python -m unittest discover -s tests -t .
```

覆盖场景（35 项）：

* 题面示例（缺关联对象经键合并补回必然答案）及无确定答案对照组；
* 递归：传递闭包、带环图终止与去重；
* 未知对象被键合并（空对象↔空对象、空对象↔常量）后才触发连接；
* 常量冲突：事实直接冲突、规则推导引发冲突、复合键/全键区分；
* 无确定答案时匿名对象不得作为答案（任一分量匿名即整元组排除）；
* UTF-8 元组序排序、去重、空字符串与多字节 Unicode 常量、空事实；
* 非法输入字段定位（布尔冒充整数、rank 越界/等长、键空/重复/越界、
  未知关系、元数不符、非 ASCII 变量名、rank 安全违规、投影变量
  不在 body、缺字段/多字段等）并整次拒绝；
* CLI：成功原子替换、非法输入保留旧输出、`inconsistent` 正常落盘、
  输入缺失时不产生输出。
