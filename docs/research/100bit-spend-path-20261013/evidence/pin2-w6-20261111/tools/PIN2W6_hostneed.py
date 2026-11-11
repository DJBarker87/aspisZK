"""Modules W6 needs from host phase 1: the PIN2-affected non-fixture-data
modules (not downstream of RPz8_JFx_Data*, no object in overlay-PIN2) in the
import closure of the fixture-named modules, in import order, grouped by
priority tier: (1) closure of the statement layer and the 30 W5-blocked
in-closure modules, (2) the rest of the fixture's needs.
usage: python3 -I PIN2W6_hostneed.py <scan_dir> <out.tsv>"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
out = sys.argv[2]; sys.argv = sys.argv[:2]
import PIN2W6_ready as R
EV = '/Users/dominic/ZK/.worktrees/pin2-lean/docs/research/100bit-spend-path-20261013/evidence'
B = [b['module'] for b in json.load(open(EV + '/pin2-w5-20261111/BLOCKED.json')) if b['in_closure']]
T1 = B + ['NDO_JFp_SHADigest', 'NDO_JFs_SerializerCanonical', 'NDO_JFy_PublicCanonical', 'NDO_JFu_PublicSemantic']
T2 = sorted(m for m in R.dep if R.FIX.match(m))
def deps(x): return R.imps(x) if x in R.dep else R.rel.get(x, [])
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in deps(m):
        if not R.sat(d): visit(d)
    if m not in R.dep and not R.sat(m): order.append(m)
tier = {}
for i, T in ((1, T1), (2, T2)):
    for m in T:
        visit(m)
    for m in order:
        tier.setdefault(m, i)
with open(out, 'w') as f:
    f.write('pos\tmodule\ttier\n')
    for i, m in enumerate(order, 1): f.write(f'{i}\t{m}\t{tier[m]}\n')
print(len(order), 'modules; tier1', sum(1 for m in order if tier[m] == 1))
