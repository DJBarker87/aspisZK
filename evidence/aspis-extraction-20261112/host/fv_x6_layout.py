#!/usr/bin/env python3
"""X6 repository layout of the ported carried library (reads only, writes <outdir>).
  <outdir>/lean-lib/<Module/Path>.lean   copy of every carried module's ported source except the Aspis chain modules
  <outdir>/MANIFEST.tsv                  one row per module of lean-lib:
      module, path (relative to lean-lib), kind (vendored | earlier-maths | base), origin (source path the carried text
      was made from), sha256_origin (the L187 / CompPoly original; empty for a base module), sha256_carried_4_32
      (after trimming and drops, the text compiled under Lean 4.32.0), sha256_ported (the file in lean-lib), edits:
        import lines replaced: `-old` / `+new` import lines between origin and carried text (trim_imports.py);
        stub import added: `+import AspisLib_Namespaces` among them (STUB_MAP);
        declarations dropped: names from the drop list for this module (drop_decls.py), and `#print` lines removed;
        port: the port classification (declarations and class) when the ported text differs from the carried text;
        removed: listed in removed.txt (module not in lean-lib)
Usage: fv_x6_layout.py <carried-table.tsv> <carried-src> <ported-src> <drop-decls.tsv> <port-classification.tsv> <outdir>
"""
import hashlib, os, shutil, sys

tab, carried, ported, drops, cls, out = sys.argv[1:7]
rows = [l.rstrip("\n").split("\t") for l in open(tab)]
h = rows[0]
D = {}
for l in open(drops):
    t = l.rstrip("\n").split("\t")
    if len(t) >= 2:
        D.setdefault(t[0], []).append(t[1])
C = {}
for l in open(cls):
    if l.startswith("#") or not l.strip():
        continue
    t = l.rstrip("\n").split("\t")
    C[t[0]] = (t[1], t[2])


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest() if p and os.path.exists(p) else ""


def imports(p):
    return [l.rstrip("\n") for l in open(p, encoding="utf-8") if l.split()[:1] == ["import"] or l.split()[:2] == ["public", "import"]]


os.makedirs(os.path.join(out, "lean-lib"), exist_ok=True)
man = open(os.path.join(out, "MANIFEST.tsv"), "w")
man.write("module\tpath\tkind\torigin\tsha256_origin\tsha256_carried_4_32\tsha256_ported\tedits\n")
removed = []
n = 0
for r in rows[1:]:
    d = dict(zip(h, r))
    m, k = d["module"], d["kind"]
    if k == "a":
        continue
    rel = m.replace(".", "/") + ".lean"
    pc, pp = os.path.join(carried, rel), os.path.join(ported, rel)
    origin = d["origin"]
    kind = {"b": "vendored", "c": "earlier-maths", "base": "base"}[k]
    so = "" if kind == "base" else sha(origin)
    if kind != "base" and "/x6/trimmed/" in origin:
        # trimmed copy: the original is the L187 source of the same module
        L = "/home/dombarker/project-offloads/codex-cx-replay-l187-20261109/src/" + rel
        origin, so = L, sha(L)
    edits = []
    if kind == "base":
        edits.append("base module (aspis-lib6/bases), no L187 original")
    elif so and so != sha(pc):
        oi, ci = imports(origin), imports(pc)
        rem = [x for x in oi if x not in ci]
        add = [x for x in ci if x not in oi]
        stub = [x for x in add if x.strip().endswith("AspisLib_Namespaces")]
        add = [x for x in add if x not in stub]
        if rem or add:
            edits.append("import lines replaced: " + " ".join("-" + x.split()[-1] for x in rem) + " " +
                         " ".join("+" + x.split()[-1] for x in add))
        if stub:
            edits.append("stub import added: AspisLib_Namespaces")
        if m in D:
            edits.append("declarations dropped: " + ",".join(D[m]))
    if not os.path.exists(pp):
        removed.append(m)
        edits.append("removed: " + (C.get(m, ("", "?"))[1]))
        man.write("\t".join([m, "", kind, origin, so, sha(pc), "", "; ".join(edits)]) + "\n")
        continue
    if sha(pp) != sha(pc):
        c = C.get(m, ("?", "?"))
        edits.append(f"port: {c[1]} ({c[0]})")
    dst = os.path.join(out, "lean-lib", rel)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copyfile(pp, dst)
    n += 1
    man.write("\t".join([m, rel, kind, origin, so, sha(pc), sha(dst), "; ".join(edits)]) + "\n")
man.close()
open(os.path.join(out, "removed.txt"), "w").write("\n".join(removed) + "\n")
print(f"lean-lib modules {n}; removed {removed}", file=sys.stderr)
