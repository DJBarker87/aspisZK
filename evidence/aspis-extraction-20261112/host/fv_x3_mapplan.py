#!/usr/bin/env python3
"""X3 stage C, mapped trim (design of research 6032f9ef5bd): plan the old-toolchain carrier-free build. Reads only.

Node set: the base modules (files in <bases-dir>) and every kind (c) module whose original closure reaches (d)
(reaches_d = 1). Imports of a trimmed module or a base are read from its file; other modules use the closure table.
Order: topological over the node set (ties in closure order). Check: the import closure of every node, with
trimmed copies and bases in place of the originals, is searched for kind (d) modules; every node that still
reaches one is listed with the path (expected failure). Untouched modules outside the node set keep their L187
objects, which are carrier-free when reaches_d = 0.

Usage: fv_x3_mapplan.py <closure-modules.tsv> <trimmed-dir> <bases-dir> <out-table.tsv> <out-check.tsv>
"""
import os, re, sys

cl, tdir, bdir, out, outc = sys.argv[1:6]
rows = [l.rstrip("\n").split("\t") for l in open(cl)]
h = rows[0]
R = {r[0]: dict(zip(h, r)) for r in rows[1:]}
order0 = [r[0] for r in rows[1:]]
kind = {m: R[m]["kind"] for m in R}
bases = sorted(f[:-5] for f in os.listdir(bdir) if f.endswith(".lean"))


def file_imports(p):
    res = []
    for l in open(p, encoding="utf-8", errors="replace"):
        s = l.strip()
        if s.startswith("import "):
            res.append(s[7:].strip())
    return res


def src(m):
    if m in bases:
        return os.path.join(bdir, m + ".lean")
    t = os.path.join(tdir, m.replace(".", "/") + ".lean")
    return t if os.path.isfile(t) else R[m]["path"]


def imports(m):
    p = src(m)
    if m in bases or p.startswith(tdir):
        return [i for i in file_imports(p) if i in R or i in bases]
    return [x for x in R[m]["closure_imports"].split(",") if x]


nodes = set(bases) | {m for m in R if kind[m] == "c" and R[m]["reaches_d"] == "1"}
# closure check
memo = {}


def reach_d(m, stack=()):
    if m in memo:
        return memo[m]
    if m not in bases and kind.get(m) == "d":
        memo[m] = [m]; return memo[m]
    memo[m] = None
    for i in imports(m):
        p = reach_d(i)
        if p:
            memo[m] = [m] + p; return memo[m]
    return None


# topological order
pos = {m: k for k, m in enumerate(order0)}
done, seq = set(), []


def visit(m):
    if m in done:
        return
    done.add(m)
    for i in imports(m):
        if i in nodes:
            visit(i)
    seq.append(m)


for m in sorted(nodes, key=lambda x: (pos.get(x, -1), x)):
    visit(m)
with open(out, "w") as f:
    f.write("module\tkind\tpath\tlines\tclosure_imports\n")
    for m in seq:
        p = src(m)
        n = sum(1 for _ in open(p, encoding="utf-8", errors="replace"))
        f.write(f"{m}\t{'base' if m in bases else kind[m]}\t{p}\t{n}\t{','.join(imports(m))}\n")
bad = 0
with open(outc, "w") as f:
    f.write("module\tstill_reaches_d\tpath_to_d\n")
    for m in seq:
        p = reach_d(m)
        if p:
            bad += 1
        f.write(f"{m}\t{int(bool(p))}\t{' -> '.join(p) if p else ''}\n")
print("nodes", len(seq), "still reaching d", bad, file=sys.stderr)
