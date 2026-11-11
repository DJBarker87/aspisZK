"""Why each regenerated (text-changed) W5 module is not compiled: walk its
unready imports down to the first module outside the W5 node set and
classify it.  usage: python3 -I PIN2W5_blocked.py"""
import json, re, sys, collections
from pathlib import Path
H = Path(__file__).resolve().parent
sys.path.insert(0, str(H))
import PIN2W5_ready as P
R = P.R
ready, blocked = P.plan()
def roots(m, seen=None):
    seen = seen if seen is not None else set()
    if m in seen: return set()
    seen.add(m); out = set()
    for d in blocked.get(m, []):
        if d in P.down: out |= roots(d, seen)
        else: out.add(d)
    return out
def klass(d):
    if d not in R.imp and not R.has('objs', d) and not R.has('base', d): return 'outside the release closure: generic dependency has no object (never built in the L187 closure)'
    if d in R.dep: return 'statement/serializer layer downstream of the fixture data, not yet compiled (W4 section 3: W3c PIN2_NEWGATE_r0 import clash)'
    if d in R.aff: return 'PIN2-affected non-fixture module not yet rebuilt in overlay-PIN2 (W3c chain)'
    return 'other: ' + ','.join(R.why(d))
rows = []
for m in sorted(P.changed):
    if m in ready: continue
    rs = roots(m)
    rows.append(dict(module=m, in_closure=m in R.imp, root_blockers=sorted(rs), classes=sorted({klass(d) for d in rs})))
fam = collections.Counter((re.sub(r'\d+', '#', r['module']), r['in_closure'], ' | '.join(r['classes'])) for r in rows)
for (f, c, k), n in sorted(fam.items()): print(n, f, 'closure' if c else 'outside', '::', k)
top = collections.Counter(d for r in rows for d in r['root_blockers'])
print('most frequent root blockers:', top.most_common(15))
(H / 'BLOCKED.json').write_text(json.dumps(rows, indent=1) + '\n')
