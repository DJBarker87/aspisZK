#!/usr/bin/env python3
"""X6 plan and gate (reads only); fv_x3_plan4.py with two changes:
  - roots: the 73 chain modules in the closure of AspisFailureBoundModel (host-order-model-73.txt); the four 33-row
    side modules and other chain files are not carried (lead, 2026-11-12). Bases are carried only if reached.
  - the table lists EVERY carried module (CompPoly, untouched and trimmed kind (c), bases, chain) in dependency
    order: under the new toolchain everything is compiled.
Graph: a module's imports come from its file when it is a trimmed copy, a base or a chain module, else from the
closure table. Gate: no carried module is kind (d) or omitted (both kind d in closure.tsv), none reaches one.
Usage: fv_x6_plan.py <closure.tsv> <trimmed-dir> <bases-dir> <chain-dir> <model-chain-order> <out-table> <out-gate>
"""
import collections, os, sys

cl, tdir, bdir, cdir, corder, out, outg = sys.argv[1:8]
rows = [l.rstrip("\n").split("\t") for l in open(cl)]
h = rows[0]
R = {r[0]: dict(zip(h, r)) for r in rows[1:]}
order0 = [r[0] for r in rows[1:]]
kind = {m: R[m]["kind"] for m in R}
bases = sorted(f[:-5] for f in os.listdir(bdir) if f.endswith(".lean"))
chain_all = sorted(f[:-5] for f in os.listdir(cdir) if f.endswith(".lean") and "/" not in f)
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
    p, own = src(m)
    imp[m] = [i for i in fimports(p) if i in kind] if own else [x for x in R[m]["closure_imports"].split(",") if x]
# a chain-module import that is neither a table module, a base nor a model-chain module is an error
for c in chain:
    for i in fimports(src(c)[0]):
        if i not in kind and not i.split(".")[0] in ("Mathlib", "Aesop", "Batteries", "Qq", "Lean", "Std", "Init",
                                                    "Plausible", "ProofWidgets", "Aeneas", "CompPoly"):
            print(f"WARNING chain {c} imports {i}, not carried", file=sys.stderr)

carried, st = set(), list(chain)
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


pos = {m: k for k, m in enumerate(order0)}
done, seq = set(), []


def visit(m):
    if m in done:
        return
    done.add(m)
    for i in imp.get(m, []):
        if i in carried:
            visit(i)
    seq.append(m)


sys.setrecursionlimit(100000)
for m in sorted(carried - set(chain), key=lambda x: (pos.get(x, -1), x)):
    visit(m)
for m in chain:
    visit(m)
with open(out, "w") as f:
    f.write("module\tkind\tpath\tlines\tclosure_imports\ttrimmed\n")
    for m in seq:
        p, own = src(m)
        f.write(f"{m}\t{kind[m]}\t{p}\t{sum(1 for _ in open(p, errors='replace'))}\t"
                f"{','.join(i for i in imp[m] if i in carried)}\t{int(own and kind[m] == 'c')}\n")
bad = 0
with open(outg, "w") as f:
    f.write("module\tkind\tpath_to_d_or_omitted\n")
    for m in seq:
        p = path_to_d(m)
        bad += bool(p)
        f.write(f"{m}\t{kind.get(m)}\t{' -> '.join(p) if p else ''}\n")
kc = collections.Counter(kind.get(m) for m in carried)
print(f"carried {len(carried)} {dict(sorted(kc.items()))}; bases not reached "
      f"{sorted(set(bases) - carried)}; gate violations {bad}", file=sys.stderr)
if bad:
    sys.exit(7)
