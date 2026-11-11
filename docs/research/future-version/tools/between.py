import os, re, sys, json
src, T = sys.argv[1], sys.argv[2]
imp = re.compile(r'^import\s+(\S+)', re.M)
local = {f[:-5] for f in os.listdir(src) if f.endswith('.lean')}
deps = {}
for m in local:
    deps[m] = [i for i in imp.findall(open(os.path.join(src, m + '.lean'), errors='replace').read()) if i in local]
import functools, sys
sys.setrecursionlimit(100000)
rev = {m: [] for m in local}
for m, ds in deps.items():
    for d in ds: rev[d].append(m)
def up(start):
    seen = set(); st = [start]
    while st:
        x = st.pop()
        for y in rev[x]:
            if y not in seen: seen.add(y); st.append(y)
    return seen
cls = json.load(open(f"{T}/classes.json"))
klass = {}
for layer in cls.values():
    for k, L in layer.items():
        for m in L: klass[m] = k
base = "Frozen2StartChargeProbability"
above = up(base)
def closure(r):
    seen=set(); st=[r]
    while st:
        x=st.pop()
        if x in seen: continue
        seen.add(x); st.extend(deps.get(x,[]))
    return seen
res = {}
for root in ["RPz7_F3T_Numeric", "TAS_FinalB"]:
    B = closure(root) & (above | {root})
    cnt = {}
    for m in B: cnt.setdefault(klass.get(m,'?'), []).append(m)
    res[root] = {k: sorted(v) for k, v in cnt.items()}
    print(root, len(B), {k: len(v) for k, v in cnt.items()})
json.dump(res, open(f"{T}/between.json","w"), indent=0)
