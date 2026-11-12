#!/usr/bin/env python3
"""X3 revision-4 plan and gate (reads only).

Graph: a module's imports come from its file when it is a trimmed copy, a base or a (trimmed) chain module, else
from the closure table. Carried set: the import closure of the chain modules (and the bases). Gate: no carried
module may be a kind (d) module or an omitted module (both have kind d in closure3.tsv). Outputs:
  <out-table>   modules to compile, dependency order: bases, every carried kind (c) module that is a trimmed copy or
                whose original closure reached (d), then the chain (columns module, kind, path, lines, closure_imports)
  <out-link>    carried kind (c) modules that are unchanged and outside the compile table: their L187 objects are
                hardlinked into the object directory that replaces L187 `objs` on LEAN_PATH
  <out-gate>    module, carried, kind, path from the module to a kind (d) or omitted module (empty when clean)
Usage: fv_x3_plan4.py <closure3.tsv> <trimmed-dir> <bases-dir> <chain-dir> <chain-order> <out-table> <out-link> <out-gate>
"""
import collections, os, sys

cl, tdir, bdir, cdir, corder, out, outl, outg = sys.argv[1:9]
rows = [l.rstrip("\n").split("\t") for l in open(cl)]
h = rows[0]
R = {r[0]: dict(zip(h, r)) for r in rows[1:]}
order0 = [r[0] for r in rows[1:]]
kind = {m: R[m]["kind"] for m in R}
bases = sorted(f[:-5] for f in os.listdir(bdir) if f.endswith(".lean"))
chain = [l.strip() for l in open(corder) if l.strip()]
for b in bases:
    kind[b] = "base"
for c in chain:
    kind[c] = "a"


def fimports(p):
    return [l.strip()[7:].strip() for l in open(p, encoding="utf-8", errors="replace") if l.strip().startswith("import ")]


def src(m):
    if m in bases:
        return os.path.join(bdir, m + ".lean"), True
    if m in chain:
        return os.path.join(cdir, m + ".lean"), True
    t = os.path.join(tdir, m.replace(".", "/") + ".lean")
    if os.path.isfile(t):
        return t, True
    return R[m]["path"], False


imp = {}
for m in list(R) + bases + chain:
    p, own = src(m) if (m in R or m in bases or m in chain) else (None, False)
    if own:
        imp[m] = [i for i in fimports(p) if i in kind]
    else:
        imp[m] = [x for x in R[m]["closure_imports"].split(",") if x]

carried, st = set(), list(chain) + bases
while st:
    x = st.pop()
    if x in carried:
        continue
    carried.add(x); st += imp.get(x, [])


def path_to_d(m):
    prev, q = {m: None}, collections.deque([m])
    while q:
        x = q.popleft()
        if kind.get(x) == "d":
            p = []
            while x is not None:
                p.append(x); x = prev[x]
            return p[::-1]
        for y in imp.get(x, []):
            if y not in prev:
                prev[y] = x; q.append(y)
    return None


compile_set = set(bases) | set(chain) | {m for m in carried if kind.get(m) == "c" and
                                         (src(m)[1] or R[m]["reaches_d"] == "1")}
pos = {m: k for k, m in enumerate(order0)}
done, seq = set(), []


def visit(m):
    if m in done:
        return
    done.add(m)
    for i in imp.get(m, []):
        if i in compile_set:
            visit(i)
    seq.append(m)


for m in sorted(compile_set - set(chain), key=lambda x: (pos.get(x, -1), x)):
    visit(m)
for m in chain:
    visit(m)
with open(out, "w") as f:
    f.write("module\tkind\tpath\tlines\tclosure_imports\n")
    for m in seq:
        p = src(m)[0]
        f.write(f"{m}\t{kind[m]}\t{p}\t{sum(1 for _ in open(p, errors='replace'))}\t{','.join(imp[m])}\n")
link = sorted(m for m in carried if kind.get(m) == "c" and m not in compile_set)
with open(outl, "w") as f:
    f.write("\n".join(link) + "\n")
bad = 0
with open(outg, "w") as f:
    f.write("module\tcarried\tkind\tpath_to_d_or_omitted\n")
    for m in sorted(set(R) | set(bases) | set(chain), key=lambda x: (pos.get(x, 10**6), x)):
        if m not in carried and m not in compile_set:
            continue
        p = path_to_d(m) if kind.get(m) != "d" else [m]
        bad += bool(p)
        f.write(f"{m}\t{int(m in carried)}\t{kind.get(m)}\t{' -> '.join(p) if p else ''}\n")
kc = collections.Counter(kind.get(m) for m in carried)
lines = sum(int(R[m]["lines"]) for m in carried if m in R and kind[m] != "a")
print(f"carried {len(carried)} {dict(kc)} lines(non-chain) {lines}; compile {len(seq)}; link {len(link)}; "
      f"gate violations {bad}", file=sys.stderr)
