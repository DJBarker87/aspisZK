#!/usr/bin/env python3
"""X3 step 3: append the Aspis chain modules (in the given order) to the mapped node table, with imports read from
the chain files, and check by import graph that no chain module reaches a kind (d) module once the trimmed copies
and the bases replace the originals. Reads only.
Usage: fv_x3_chainplan.py <closure-modules.tsv> <map-table.tsv> <chain-dir> <order.txt> <out-table> <out-check>"""
import os, sys

cl, mt, cdir, order, out, outc = sys.argv[1:7]
rows = [l.rstrip("\n").split("\t") for l in open(cl)]
h = rows[0]
R = {r[0]: dict(zip(h, r)) for r in rows[1:]}
kind = {m: R[m]["kind"] for m in R}
imp = {m: [x for x in R[m]["closure_imports"].split(",") if x] for m in R}
mrows = [l.rstrip("\n").split("\t") for l in open(mt)]
for x in mrows[1:]:
    imp[x[0]] = [i for i in x[4].split(",") if i]
    kind.setdefault(x[0], "base")
chain = [l.strip() for l in open(order) if l.strip()]
for m in chain:
    kind[m] = "a"
    p = os.path.join(cdir, m + ".lean")
    imp[m] = [l.strip()[7:].strip() for l in open(p, encoding="utf-8") if l.strip().startswith("import ")]
    imp[m] = [i for i in imp[m] if i in kind or i in chain]


def reach(m, seen):
    if kind.get(m) == "d":
        return [m]
    if m in seen:
        return None
    seen.add(m)
    for i in imp.get(m, []):
        p = reach(i, seen)
        if p:
            return [m] + p
    return None


with open(out, "w") as f:
    f.write("\t".join(mrows[0]) + "\n")
    for x in mrows[1:]:
        f.write("\t".join(x) + "\n")
    for m in chain:
        p = os.path.join(cdir, m + ".lean")
        f.write(f"{m}\ta\t{p}\t{sum(1 for _ in open(p))}\t{','.join(imp[m])}\n")
bad = 0
with open(outc, "w") as f:
    f.write("module\tstill_reaches_d\tpath_to_d\n")
    for m in chain:
        p = reach(m, set())
        bad += bool(p)
        f.write(f"{m}\t{int(bool(p))}\t{' -> '.join(p) if p else ''}\n")
print("chain", len(chain), "reaching d", bad, file=sys.stderr)
