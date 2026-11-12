#!/usr/bin/env python3
"""X3: list every `open` line in the carried sources (compile table + hardlinked unchanged modules) that names the
namespace of a carrier or omitted module. Such a namespace no longer exists in the carrier-free object set when no
remaining module declares in it, and neither trim_imports.py nor drop_decls.py edits `open` lines. Reads only.
Usage: fv_x3_opens.py <x3-dir> <out.tsv>"""
import re, sys

X, out = sys.argv[1], sys.argv[2]
gone = {l.split("\t")[0] for l in list(open(X + "/closure/d-report.tsv"))[1:]}
gone |= {l.strip() for l in open(X + "/omit4.txt") if l.strip()}
plan = [l.rstrip("\n").split("\t") for l in list(open(X + "/closure/plan4-table.tsv"))[1:]]
link = [l.strip() for l in open(X + "/closure/plan4-link.txt") if l.strip()]
rows = [l.rstrip("\n").split("\t") for l in open(X + "/closure/closure-modules.tsv")]
path = {r[0]: r[4] for r in rows[1:]}
srcs = [(p[0], p[2]) for p in plan] + [(m, path[m]) for m in link]
res = []
for m, p in srcs:
    for i, l in enumerate(open(p, errors="replace"), 1):
        if re.match(r"\s*open\b", l):
            toks = re.findall(r"[A-Za-z_][\w.]*", l.split("--")[0])[1:]
            hit = [t for t in toks if t in gone or t.split(".")[-1] in gone]
            if hit:
                res.append("\t".join([m, str(i), ",".join(hit), l.strip()]))
with open(out, "w") as f:
    f.write("module\tline\tremoved_namespaces\topen_line\n" + "\n".join(res) + "\n")
print(len(res))
print("\n".join(res))
