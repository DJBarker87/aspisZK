#!/usr/bin/env python3
"""X6: compile table of the ported tree. Keeps the dependency order of closure/carried-table.tsv, drops a module
whose file is absent from the ported tree (a removed vendored file), and re-reads every module's imports from its
ported file (restricted to table modules), so an import edit in a port patch is followed. Fails if an import names
a removed module or the order is broken.
Usage: fv_x6_table.py <carried-table.tsv> <ported-src> <out-table.tsv>
"""
import os, sys

tab, root, out = sys.argv[1:4]
rows = [l.rstrip("\n").split("\t") for l in open(tab)]
h = rows[0]
mi, ki = h.index("module"), h.index("kind")
mods = [r[mi] for r in rows[1:]]
present = {m for m in mods if os.path.isfile(os.path.join(root, m.replace(".", "/") + ".lean"))}
removed = [m for m in mods if m not in present]
seen, bad = set(), []
with open(out, "w") as f:
    f.write("module\tkind\tpath\tlines\tclosure_imports\n")
    for r in rows[1:]:
        m = r[mi]
        if m not in present:
            continue
        p = os.path.join(root, m.replace(".", "/") + ".lean")
        txt = open(p, encoding="utf-8", errors="replace").read().split("\n")
        imps = []
        for l in txt:
            t = l.strip().split()
            if not t:
                continue
            if t[0] == "import" or (len(t) > 1 and t[0] == "public" and t[1] == "import"):
                name = t[-1]
                if name in removed:
                    bad.append(f"{m} imports removed {name}")
                if name in present:
                    imps.append(name)
                    if name not in seen:
                        bad.append(f"{m} imports {name} before it is compiled")
        seen.add(m)
        f.write(f"{m}\t{r[ki]}\t{p}\t{len(txt)}\t{','.join(imps)}\n")
print(f"modules {len(present)} removed {removed}", file=sys.stderr)
if bad:
    print("\n".join(bad), file=sys.stderr); sys.exit(5)
