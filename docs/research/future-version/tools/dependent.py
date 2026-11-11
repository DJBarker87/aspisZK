"""Modules of the bound layer (import closure of Frozen2StartChargeProbability)
that import, directly or transitively, one of the R1 definitions the Aspis
40-row instance replaces; and which of those mention 33 or 34 in code.

usage: python3 -I dependent.py <l187-src> <dir with classes.json>
"""
import os, re, sys, json
src, T = sys.argv[1], sys.argv[2]
imp = re.compile(r'^import\s+(\S+)', re.M)
local = {f[:-5] for f in os.listdir(src) if f.endswith('.lean')}
deps = {m: [i for i in imp.findall(open(f'{src}/{m}.lean', errors='replace').read()) if i in local] for m in local}
rev = {m: [] for m in local}
for m, ds in deps.items():
    for d in ds: rev[d].append(m)
def up(starts):
    seen = set(starts); st = list(starts)
    while st:
        x = st.pop()
        for y in rev[x]:
            if y not in seen: seen.add(y); st.append(y)
    return seen
cls = json.load(open(f'{T}/classes.json'))['A_restricted_union_bound']
A = set(sum(cls.values(), []))
klass = {m: k for k, L in cls.items() for m in L}
changed = ['R1UnifiedSampler', 'R1LiteralClassifier', 'R1UnifiedDecoder', 'R1LiteralByteProtocol', 'R1UnifiedLabels']
D = up(changed) & A
cnt = {}
for m in D: cnt.setdefault(klass[m], []).append(m)
print('bound layer', len(A), 'dependent', len(D), {k: len(v) for k, v in cnt.items()}, 'independent', len(A - D))
hc = [m for m in D if re.search(r'List\.range 33|< 33|≤ 33|\b33\b|\b34\b|Fin 33',
      re.sub(r'/-.*?-/', '', open(f'{src}/{m}.lean', errors='replace').read(), flags=re.S))]
print('dependent and mentioning 33/34 in code', len(hc))
json.dump({k: sorted(v) for k, v in cnt.items()}, open(f'{T}/dependent.json', 'w'), indent=0)
json.dump(sorted(hc), open(f'{T}/hardcoded.json', 'w'))
