#!/usr/bin/env python3
"""importsize.py ENV.json OBJECTS SOURCES MOD [MOD...]
Transitive import closure of the given modules (resolved like run2.py: OBJECTS
first, then LEAN_PATH), with per-module .olean sizes. Prints closure total,
per-root breakdown, and the per-package totals. Read-only."""
import os, sys, json, re
env = json.load(open(sys.argv[1])); objects, sources = sys.argv[2], sys.argv[3]
mods = sys.argv[4:]
lp = [objects] + env["LEAN_PATH"].split(":")
sp = [sources] + env["LEAN_SRC_PATH"].split(":") + [p for p in env["LEAN_PATH"].split(":")]
# src path: for packages, .lake/build/lib/lean -> package root
pk = []
for p in env["LEAN_PATH"].split(":"):
    if p.endswith("/.lake/build/lib/lean"): pk.append(p[:-len("/.lake/build/lib/lean")])
    else: pk.append(p.replace("/lib/lean", "/src/lean"))
sp = [sources] + pk + [x for x in os.environ.get("EXTRA_SRC", "").split(":") if x]
def olean(m):
    rel = m.replace(".", "/") + ".olean"
    for d in lp:
        f = os.path.join(d, rel)
        if os.path.exists(f): return f
    return None
def src(m):
    rel = m.replace(".", "/") + ".lean"
    for d in sp:
        f = os.path.join(d, rel)
        if os.path.exists(f): return f
    return None
IMP = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.«»]+)')
cache = {}
def imports(m):
    if m in cache: return cache[m]
    f = src(m); r = []
    if f:
        for line in open(f, errors="replace"):
            s = line.strip()
            if s.startswith("import") or s.startswith("public") or s.startswith("meta") or s.startswith("private import"):
                mm = IMP.match(line)
                if mm: r.append(mm.group(1))
            elif s and not s.startswith("--") and not s.startswith("/-") and not s.startswith("module") and not s.startswith("prelude") and r:
                break
    cache[m] = r; return r
def closure(roots):
    seen = set(); st = list(roots)
    while st:
        m = st.pop()
        if m in seen: continue
        seen.add(m); st.extend(imports(m))
    return seen
def size(m):
    f = olean(m); return os.path.getsize(f) if f else 0
def pkg(m):
    f = olean(m) or ""
    if f.startswith(objects): return "objects2:" + m.split(".")[0]
    for k in ["mathlib", "batteries", "aesop", "Qq", "proofwidgets", "plausible", "importGraph", "LeanSearchClient", "Cli"]:
        if "/packages/" + k + "/" in f: return k
    if "/toolchains/" in f: return "lean-core"
    if "AspisFormal/.lake/build" in f: return "AspisFormal"
    return "MISSING" if not f else f
C = closure(mods)
tot = sum(size(m) for m in C)
print(f"closure of {mods}: {len(C)} modules, {tot/1e9:.3f} GB olean")
bp = {}
for m in C: bp.setdefault(pkg(m), [0, 0]); bp[pkg(m)][0] += size(m); bp[pkg(m)][1] += 1
for k, (s, n) in sorted(bp.items(), key=lambda x: -x[1][0]): print(f"  {k:40s} {n:6d} mods {s/1e9:7.3f} GB")
print("whole-Mathlib importers in closure:", sorted(m for m in C if "Mathlib" in imports(m)))
missing = sorted(m for m in C if not olean(m)); print("missing oleans:", missing[:20])
nos = sorted(m for m in C if not src(m)); print("no source found (imports not followed):", len(nos), nos[:40])
if os.environ.get("PERROOT"):
    for r in mods:
        for d in imports(r):
            c = closure([d]); print(f"  {r} <- {d}: {len(c)} mods {sum(size(x) for x in c)/1e9:.3f} GB")
if os.environ.get("TOP"):
    big = sorted(((size(m), m) for m in C), reverse=True)[:int(os.environ["TOP"])]
    for s, m in big: print(f"    {s/1e6:9.1f} MB {m}")
if os.environ.get("TABLE"):
    print("\nmodule | closure mods | olean GB | whole Mathlib? | first whole-Mathlib importers")
    for m in os.environ["TABLE"].split(","):
        c = closure([m]); wm = "Mathlib" in c
        imps = sorted(x for x in c if "Mathlib" in imports(x))
        print(f"{m} | {len(c)} | {sum(size(x) for x in c)/1e9:.3f} | {wm} | {imps[:6]}")
if os.environ.get("DIFF"):
    a, b = os.environ["DIFF"].split("|")
    A = closure(a.split(",")); Bc = closure(b.split(","))
    d = Bc - A
    print(f"\nclosure({b}) - closure({a}): {len(d)} mods, {sum(size(x) for x in d)/1e9:.3f} GB")
    g = {}
    for x in d:
        k = ".".join(x.split(".")[:2]); g.setdefault(k, [0, 0]); g[k][0] += 1; g[k][1] += size(x)
    for k, (n, s) in sorted(g.items(), key=lambda t: -t[1][1])[:40]: print(f"   {k:45s} {n:5d} {s/1e6:8.1f} MB")
