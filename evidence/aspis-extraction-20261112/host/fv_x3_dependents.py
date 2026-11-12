#!/usr/bin/env python3
"""X3: for each closure module, how many closure modules depend on it transitively. Reads only.
Usage: fv_x3_dependents.py <closure-modules.tsv> <out.tsv>"""
import collections, sys

src, out = sys.argv[1], sys.argv[2]
lines = [l.rstrip("\n").split("\t") for l in open(src)]
H, rows = lines[0], lines[1:]
R = {r[0]: dict(zip(H, r)) for r in rows}
order = [r[0] for r in rows]  # dependency order
imp = {m: [x for x in R[m]["closure_imports"].split(",") if x] for m in order}
anc = {}
for m in order:
    s = set()
    for i in imp[m]:
        s.add(i); s |= anc[i]
    anc[m] = s
dep = collections.Counter()
for m in order:
    for a in anc[m]:
        dep[a] += 1
direct = collections.Counter(i for m in order for i in imp[m])
with open(out, "w") as f:
    f.write("module\tkind\tlines\ttransitive_dependents_in_closure\tdirect_importers_in_closure\n")
    for m in sorted(order, key=lambda x: (-dep[x], x)):
        f.write(f"{m}\t{R[m]['kind']}\t{R[m]['lines']}\t{dep[m]}\t{direct[m]}\n")
for m, c in dep.most_common(15):
    print(m, R[m]["kind"], R[m]["lines"], c, direct[m])
for k in "abcd":
    ms = [m for m in order if R[m]["kind"] == k]
    print("kind", k, len(ms), "modules", sum(int(R[m]["lines"]) for m in ms), "lines")
print("total lines", sum(int(R[m]["lines"]) for m in order))
print("longest import chain depth (ancestors of the root)", len(anc[order[-1]]))
