#!/usr/bin/env python3
"""X3 trim variant ("frontier"): like ASPIS-LIB-trim_imports.py, but each removed `import D` (D of kind d) is
replaced by `import F` for every module F in D's carrier-free frontier: the non-(d) modules reached from D through
(d) modules only. Frontier modules the file already imports are not repeated. The inserted lines go where the
first removed line was; every other byte is unchanged. The difference to the plain trim is then only the
declarations made inside (d) modules, so a failure here is a use of carrier content.
Appends module, sha256 before, sha256 after, removed, added to <out>/TRIM_RECORD.tsv.
Usage: fv_x3_trim_frontier.py <src_dir> <out_dir> <closure-modules.tsv> <module>..."""
import hashlib, os, sys

src, out, table = sys.argv[1:4]
mods = sys.argv[4:]
rows = [l.rstrip("\n").split("\t") for l in open(table)]
h = rows[0]
R = {r[0]: dict(zip(h, r)) for r in rows[1:]}
kind = {m: r["kind"] for m, r in R.items()}
imps = {m: [x for x in r["closure_imports"].split(",") if x] for m, r in R.items()}


def frontier(d, seen=None):
    seen = set() if seen is None else seen
    out = []
    for i in imps[d]:
        if i in seen:
            continue
        seen.add(i)
        if kind[i] == "d":
            out += frontier(i, seen)
        else:
            out.append(i)
    return out


rec = open(os.path.join(out, "TRIM_RECORD.tsv"), "a")
for m in mods:
    p = os.path.join(src, m.replace(".", "/") + ".lean")
    txt = open(p, "rb").read()
    lines = txt.split(b"\n")
    have = set()
    for l in lines:
        s = l.decode("utf-8", "replace").strip()
        if s.startswith("import "):
            have.add(s[7:].strip())
    kept, removed, added, placed = [], [], [], False
    for l in lines:
        s = l.decode("utf-8", "replace").strip()
        if s.startswith("import ") and kind.get(s[7:].strip()) == "d":
            removed.append(s[7:].strip())
            if not placed:
                placed = True
                kept.append(None)  # placeholder
            continue
        kept.append(l)
    for d in removed:
        for f in frontier(d):
            if f not in have and f not in added:
                added.append(f)
    ins = [("import " + f).encode() for f in added]
    new_lines = []
    for l in kept:
        if l is None:
            new_lines += ins
        else:
            new_lines.append(l)
    new = b"\n".join(new_lines)
    q = os.path.join(out, m.replace(".", "/") + ".lean")
    os.makedirs(os.path.dirname(q), exist_ok=True)
    open(q, "wb").write(new)
    rec.write(f"{m}\t{hashlib.sha256(txt).hexdigest()}\t{hashlib.sha256(new).hexdigest()}\t"
              f"{','.join(removed) or '-'}\t{','.join(added) or '-'}\n")
    print(m, "removed", removed, "added", len(added))
