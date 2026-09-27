#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
multi_graph_propagate.py — 多依赖图交叉传播分析工具（纯 Python 标准库，单文件）

输入格式（行式 DSL，# 之后为注释，空行忽略）：

    graph <图名>
    <节点>: <依赖节点1> <依赖节点2> ...
    end

    xref <图A> <节点A> <图B> <节点B>     # 图A.节点A 引用 图B.节点B
    change <图> <节点> <变更类型>        # 变更操作流，按出现顺序逐条执行

语义约定：
    - “X 依赖 Y”  =>  Y 变更会波及 X（沿依赖边向依赖方传播）。
    - “A 引用 B”（xref）=>  B 变更会波及 A（跨图扩散）。
    - 传播按 BFS 进行，已访问集合保证依赖环（图内/跨图）上必然终止。
    - 同一轮中同一 (图, 节点) 的重复变更按“同轮覆盖”报错并忽略后者。

输出：
    1. 受影响节点集合（含来源操作、来源图、多源/多图合并标记）
    2. 传播轨迹（每个变更操作到每个受影响节点的完整路径，可追溯）
    3. 依赖环报告（图内环 / 跨图环，给出环上节点链）
    4. 错误清单（不存在的图/节点、跨图引用目标缺失、同轮覆盖、解析错误）

用法：
    python3 multi_graph_propagate.py 输入文件 [更多输入文件...]
    python3 multi_graph_propagate.py --demo          # 运行内置自测样例
    python3 multi_graph_propagate.py --emit-sample   # 打印样例输入（可重定向保存）
"""

import sys
from collections import defaultdict, deque


def fmt(node):
    """('G1', 'A') -> 'G1.A'"""
    return "%s.%s" % node


class Model:
    def __init__(self):
        self.graphs = {}    # 图名 -> {节点: set(依赖节点)}
        self.xrefs = []     # (源图, 源节点, 目标图, 目标节点, 行号)
        self.changes = []   # (图, 节点, 变更类型, 行号)
        self.errors = []    # 解析/校验错误，按发现顺序


# ---------------------------------------------------------------- 解析

def parse(text, model):
    current = None
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if current is not None:
            if line == "end":
                current = None
                continue
            if ":" not in line:
                model.errors.append("第%d行: 依赖定义缺少 ':' -> %s" % (lineno, raw.strip()))
                continue
            node, _, deps = line.partition(":")
            node = node.strip()
            if not node:
                model.errors.append("第%d行: 节点名为空 -> %s" % (lineno, raw.strip()))
                continue
            model.graphs[current].setdefault(node, set()).update(deps.split())
            continue
        parts = line.split()
        kw = parts[0]
        if kw == "graph" and len(parts) == 2:
            name = parts[1]
            if name in model.graphs:
                model.errors.append("第%d行: 图 '%s' 重复定义" % (lineno, name))
            else:
                model.graphs[name] = {}
            current = name
        elif kw == "xref" and len(parts) == 5:
            model.xrefs.append((parts[1], parts[2], parts[3], parts[4], lineno))
        elif kw == "change" and len(parts) == 4:
            model.changes.append((parts[1], parts[2], parts[3], lineno))
        else:
            model.errors.append("第%d行: 无法解析 -> %s" % (lineno, raw.strip()))
    if current is not None:
        model.errors.append("图 '%s' 缺少 end 结束标记" % current)


# ---------------------------------------------------------------- 构建与校验

def build(model):
    """返回 (nodes_of, edges, valid_xrefs, valid_changes)。

    edges[(g, n)] = 当 (g, n) 变更时会直接被波及的全局节点集合，
    即依赖边反向 + 跨图引用边反向统一成一张全局有向图。
    """
    nodes_of = {}
    edges = defaultdict(set)
    for g, nodemap in model.graphs.items():
        members = set(nodemap)
        for node, deps in nodemap.items():
            members.update(deps)
            for d in deps:
                edges[(g, d)].add((g, node))
        nodes_of[g] = members

    valid_xrefs = []
    for g1, n1, g2, n2, lineno in model.xrefs:
        ok = True
        if g1 not in model.graphs:
            model.errors.append("第%d行: 跨图引用源图 '%s' 不存在" % (lineno, g1))
            ok = False
        elif n1 not in nodes_of[g1]:
            model.errors.append("第%d行: 跨图引用源节点 '%s' 不存在于图 '%s'" % (lineno, n1, g1))
            ok = False
        if g2 not in model.graphs:
            model.errors.append("第%d行: 跨图引用目标缺失: 图 '%s' 不存在" % (lineno, g2))
            ok = False
        elif n2 not in nodes_of[g2]:
            model.errors.append("第%d行: 跨图引用目标缺失: 节点 '%s' 不存在于图 '%s'" % (lineno, n2, g2))
            ok = False
        if ok:
            valid_xrefs.append((g1, n1, g2, n2))
            edges[(g2, n2)].add((g1, n1))

    valid_changes = []
    seen = {}
    for g, n, ctype, lineno in model.changes:
        if g not in model.graphs:
            model.errors.append("第%d行: 变更操作引用了不存在的图 '%s'" % (lineno, g))
            continue
        if n not in nodes_of[g]:
            model.errors.append("第%d行: 变更操作引用了不存在的节点 '%s'" % (lineno, fmt((g, n))))
            continue
        key = (g, n)
        if key in seen:
            first_lineno, first_type = seen[key]
            model.errors.append(
                "第%d行: 同轮覆盖: 节点 '%s' 已在第%d行登记变更(%s)，忽略本次(%s)"
                % (lineno, fmt(key), first_lineno, first_type, ctype))
            continue
        seen[key] = (lineno, ctype)
        valid_changes.append((g, n, ctype, lineno))
    return nodes_of, edges, valid_xrefs, valid_changes


# ---------------------------------------------------------------- 依赖环检测

def find_sccs(nodes, edges):
    """Tarjan 强连通分量（递归实现，按节点数放大递归上限）。"""
    sys.setrecursionlimit(max(10000, len(nodes) * 4 + 100))
    index = {}
    low = {}
    on_stack = set()
    stack = []
    counter = [0]
    sccs = []

    def strongconnect(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        for w in edges.get(v, ()):
            if w not in index:
                strongconnect(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            sccs.append(scc)

    for v in sorted(nodes):
        if v not in index:
            strongconnect(v)
    return sccs


def extract_cycle(scc, edges):
    """在一个 SCC 内提取一条具体环链 [n0, n1, ..., n0]。"""
    members = set(scc)
    start = min(members)
    if start in edges.get(start, ()):
        return [start, start]
    parent = {start: None}
    queue = deque([start])
    while queue:
        cur = queue.popleft()
        for nxt in sorted(edges.get(cur, ())):
            if nxt not in members:
                continue
            if nxt == start:
                chain = [start]
                node = cur
                while node is not None:
                    chain.append(node)
                    node = parent[node]
                chain.reverse()
                return chain
            if nxt not in parent:
                parent[nxt] = cur
                queue.append(nxt)
    return sorted(members)


# ---------------------------------------------------------------- 传播与分析

def analyze(model):
    nodes_of, edges, xrefs, changes = build(model)
    out = []

    # ---- 变更传播：BFS，visited 集合保证环上终止 ----
    affected_sources = defaultdict(list)  # 全局节点 -> [操作编号]
    op_traces = []                        # (操作编号, 源节点, 类型, {节点: 路径})
    for op_no, (g, n, ctype, _lineno) in enumerate(changes, 1):
        source = (g, n)
        parent = {source: None}
        queue = deque([source])
        while queue:
            cur = queue.popleft()
            affected_sources[cur].append(op_no)
            for nxt in sorted(edges.get(cur, ())):
                if nxt in parent:      # 已访问 -> 终止判定，环上不会死循环
                    continue
                parent[nxt] = cur
                queue.append(nxt)
        paths = {}
        for node in parent:
            chain = []
            cur = node
            while cur is not None:
                chain.append(cur)
                cur = parent[cur]
            paths[node] = list(reversed(chain))
        op_traces.append((op_no, source, ctype, paths))

    bar = "=" * 64

    # ---- 1. 受影响节点集合 ----
    out.append(bar)
    out.append("受影响节点集合（共 %d 个）" % len(affected_sources))
    out.append(bar)
    if not affected_sources:
        out.append("  （无）")
    for node in sorted(affected_sources):
        ops = affected_sources[node]
        src_graphs = sorted({changes[o - 1][0] for o in ops})
        tags = []
        if len(ops) > 1:
            tags.append("多源合并")
        if len(src_graphs) > 1:
            tags.append("多图合并")
        tag = "  [%s]" % ", ".join(tags) if tags else ""
        out.append("  %-10s 来源操作: %-22s 来源图: %s%s" % (
            fmt(node),
            " ".join("#%d(%s)" % (o, changes[o - 1][2]) for o in ops),
            ", ".join(src_graphs),
            tag))

    # ---- 2. 传播轨迹 ----
    out.append("")
    out.append(bar)
    out.append("传播轨迹（每个变更的完整影响路径，可追溯）")
    out.append(bar)
    if not op_traces:
        out.append("  （无有效变更操作）")
    for op_no, source, ctype, paths in op_traces:
        out.append("[变更 #%d] %s (%s) — 影响 %d 个节点" % (op_no, fmt(source), ctype, len(paths)))
        for node in sorted(paths, key=lambda x: (len(paths[x]), x)):
            out.append("  " + " -> ".join(fmt(p) for p in paths[node]))

    # ---- 3. 依赖环报告 ----
    all_nodes = {(g, n) for g, members in nodes_of.items() for n in members}
    sccs = find_sccs(all_nodes, edges)
    cycles = []
    for scc in sccs:
        if len(scc) > 1 or (len(scc) == 1 and scc[0] in edges.get(scc[0], ())):
            cycles.append(extract_cycle(scc, edges))
    cycles.sort(key=lambda c: [fmt(n) for n in c])
    out.append("")
    out.append(bar)
    out.append("依赖环报告（共 %d 个）" % len(cycles))
    out.append(bar)
    if not cycles:
        out.append("  无")
    for i, chain in enumerate(cycles, 1):
        kind = "跨图环" if len({g for g, _ in chain}) > 1 else "图内环"
        out.append("  环#%d (%s): %s" % (i, kind, " -> ".join(fmt(p) for p in chain)))

    # ---- 4. 错误清单 ----
    out.append("")
    out.append(bar)
    out.append("错误报告（共 %d 条）" % len(model.errors))
    out.append(bar)
    if not model.errors:
        out.append("  无")
    for e in model.errors:
        out.append("  - " + e)

    return "\n".join(out)


# ---------------------------------------------------------------- 自测样例

DEMO_INPUT = """\
# ===== 图定义：每行 “节点: 依赖节点列表” =====
graph G1
A: B C
B: D
C:
D:
end

graph G2
X: Y
Y: Z
Z:
end

# 图内环：P -> Q -> R -> P
graph G3
P: Q
Q: R
R: P
end

# ===== 跨图引用：xref 源图 源节点 目标图 目标节点 =====
xref G2 X G1 A        # G2.X 引用 G1.A（G1.A 变更波及 G2.X）
xref G2 Z G1          # 字段不足：演示解析错误
xref G2 Z G1 A        # 与下一条构成跨图环 G1.A -> G2.Z -> G2.Y -> G1.D -> G1.B -> G1.A
xref G1 D G2 Y
xref G2 X G1 NOPE     # 跨图引用目标节点缺失
xref G2 X G8 A        # 跨图引用目标图缺失

# ===== 变更操作流：change 图 节点 变更类型 =====
change G1 B modify
change G2 Z add
change G1 B delete    # 同轮覆盖：G1.B 已有变更
change G9 Q modify    # 图不存在
change G1 Q modify    # 节点不存在
"""


def main(argv):
    if argv == ["--emit-sample"]:
        sys.stdout.write(DEMO_INPUT)
        return 0
    if not argv or argv == ["--demo"]:
        text, name = DEMO_INPUT, "<内置自测样例>"
    else:
        parts = []
        for path in argv:
            with open(path, encoding="utf-8") as fh:
                parts.append(fh.read())
        text = "\n".join(parts)
        name = ", ".join(argv)
    model = Model()
    parse(text, model)
    print("输入: %s" % name)
    print("图: %s" % (", ".join(sorted(model.graphs)) or "（无）"))
    print()
    print(analyze(model))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
