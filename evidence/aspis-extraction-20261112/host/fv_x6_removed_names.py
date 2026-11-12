#!/usr/bin/env python3
"""X6: occurrences of Mathlib names that no longer exist in Mathlib 9d581dff, in every carried source, classified
as statement text (before the declaration's `:=`/`where`, split by fv_x6_stmtcheck.decls) or proof body.
Names: the removed names the port's error logs showed (argument list). Output: module, line, position (statement |
proof | outside declaration), declaration kind, declaration name, name, line text.
Usage: fv_x6_removed_names.py <carried-src> <name> [<name> ...]"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fv_x6_stmtcheck import decls, strip_comments
root, names = sys.argv[1], sys.argv[2:]
pat = re.compile("|".join(r"(?<![\w.])" + re.escape(n) + r"(?![\w])" for n in names))
print("module\tline\tposition\tdecl_kind\tdecl_name\tname\ttext")
for dp, _, fs in os.walk(root):
    for f in sorted(fs):
        if not f.endswith(".lean"):
            continue
        p = os.path.join(dp, f); m = os.path.relpath(p, root)[:-5].replace("/", ".")
        txt = open(p, encoding="utf-8").read()
        clean = strip_comments(txt).split("\n")
        ds = decls(txt)
        for k, l in enumerate(clean, 1):
            for mo in pat.finditer(l):
                enc = [d for d in ds if d[3] <= k]
                if not enc:
                    pos, dk, dn = "outside declaration", "", ""
                else:
                    d = enc[-1]; dk, dn = d[0], d[1]
                    pos = "statement" if k < d[4] or (k == d[4] and mo.start() < (l.find(":=") if ":=" in l else 10**9)) else "proof"
                print(f"{m}\t{k}\t{pos}\t{dk}\t{dn}\t{mo.group(0)}\t{l.strip()[:160]}")
