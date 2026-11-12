#!/usr/bin/env python3
"""X6 records (reads only; writes into <outdir>):
  port-patches/<Module>.diff   `diff -u` of the carried (4.32) source against the ported source, paths relative to
                               the tree roots (carried-src/..., ported-src/...); a removed module diffs against
                               /dev/null
  port-patches.tsv             one row per patched module: module, kind (vendored | earlier-maths), declarations,
                               error kind, lines removed, lines added, compiles under 4.36.0-rc2, compiles under 4.32.0,
                               note. Classification columns come from <classification.tsv> (module, declarations,
                               error_kind, note), the compile columns from <new-result.tsv> and <old-result.tsv>.
  port-compile.tsv             one row per module of the compile table: module, kind, result (compiled | patched-
                               compiled | reused-x3-pass2 | failed | skipped), wall s, peak RSS kB, errors, first error
                               (the LAST row of each module in <new-result.tsv>, resumed rows resolved to their origin)
Usage: fv_x6_records.py <carried-src> <ported-src> <compile-table.tsv> <new-result.tsv> <old-result.tsv|-> \
                        <classification.tsv> <outdir>
"""
import difflib, os, sys

old_root, new_root, table, newres, oldres, cls, out = sys.argv[1:8]
os.makedirs(os.path.join(out, "port-patches"), exist_ok=True)
kinds = {}
for l in list(open(table))[1:]:
    r = l.rstrip("\n").split("\t")
    kinds[r[0]] = r[1]
C = {}
for l in open(cls):
    if l.startswith("#") or not l.strip():
        continue
    r = l.rstrip("\n").split("\t")
    C[r[0]] = r[1:]


def last_rows(path):
    rows = {}
    if path == "-" or not os.path.exists(path):
        return rows
    for l in open(path):
        r = l.rstrip("\n").split("\t")
        rows[r[0]] = r
    return rows


NEW, OLD = last_rows(newres), last_rows(oldres)
changed = []
for dp, _, fs in os.walk(old_root):
    for f in fs:
        if not f.endswith(".lean"):
            continue
        rel = os.path.relpath(os.path.join(dp, f), old_root)
        m = rel[:-5].replace("/", ".")
        a = open(os.path.join(old_root, rel), encoding="utf-8").read()
        pn = os.path.join(new_root, rel)
        b = open(pn, encoding="utf-8").read() if os.path.exists(pn) else None
        if a != b:
            changed.append((m, rel, a, b))
rows = []
for m, rel, a, b in sorted(changed):
    al = a.splitlines(keepends=True)
    bl = b.splitlines(keepends=True) if b is not None else []
    d = list(difflib.unified_diff(al, bl, "carried-src/" + rel, ("ported-src/" + rel) if b is not None else "/dev/null", n=3))
    open(os.path.join(out, "port-patches", m + ".diff"), "w").write("".join(d))
    rem = sum(1 for x in d if x.startswith("-") and not x.startswith("---"))
    add = sum(1 for x in d if x.startswith("+") and not x.startswith("+++"))
    k = kinds.get(m, "b" if m.startswith("CompPoly.") else "?")
    kind = {"b": "vendored", "c": "earlier-maths", "a": "aspis-chain", "base": "base"}.get(k, k)
    c = C.get(m, ["?", "?", ""])
    nr = NEW.get(m)
    new_ok = "removed" if b is None else ("yes" if nr and nr[2] in ("0",) else ("no" if nr and nr[2] not in ("skipped",) else "not reached"))
    orr = OLD.get(m)
    old_ok = "removed" if b is None else ("yes" if orr and orr[2] == "0" else ("no" if orr else "not tested"))
    rows.append([m, kind, c[0], c[1], str(rem), str(add), new_ok, old_ok, c[2] if len(c) > 2 else ""])
with open(os.path.join(out, "port-patches.tsv"), "w") as f:
    f.write("module\tkind\tdeclarations\terror_kind\tlines_removed\tlines_added\tcompiles_4_36_0_rc2\tcompiles_4_32_0\tnote\n")
    for r in rows:
        f.write("\t".join(r) + "\n")
patched = {r[0] for r in rows}
with open(os.path.join(out, "port-compile.tsv"), "w") as f:
    f.write("module\tkind\tresult\twall_s\tpeak_rss_kb\terrors\tfirst_error\n")
    for l in list(open(table))[1:]:
        m = l.split("\t")[0]
        r = NEW.get(m)
        if r is None:
            f.write(f"{m}\t{kinds[m]}\tnot reached\t\t\t\t\n"); continue
        st = r[2]
        res = {"0": "patched-compiled" if m in patched else "compiled", "skipped": "skipped",
               "reused-x3-pass2": "reused-x3-pass2"}.get(st, "failed")
        first = r[6].replace("/home/dombarker/project-offloads/future-version-20261111/x6/ported-src/", "") if len(r) > 6 else ""
        if st == "skipped":
            first = r[6] if len(r) > 6 else ""
        f.write("\t".join([m, r[1], res, r[3] if len(r) > 3 else "", r[4] if len(r) > 4 else "",
                           r[5] if len(r) > 5 else "", first[:300]]) + "\n")
print(f"patched modules {len(rows)}", file=sys.stderr)
