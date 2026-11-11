"""Compile planning for the W5 set.  Nodes: every regenerated source with
changed text, plus every module downstream of one (by the release import
graph, closure modules only).  A node is ready when each import is an
earlier node of the plan, or not a node and ready by W4's rule (present in
overlay-PIN2-W4, or untouched by PIN2 and present in objs/base).
usage: python3 -I PIN2W5_ready.py"""
import collections, json, sys, subprocess
from pathlib import Path
H = Path(__file__).resolve().parent
sys.path.insert(0, str(H.parent / 'pin2-w4-20261111'))
import PIN2W4_ready as R
REG = json.loads((H / 'REGEN-pin2.json').read_text())['modules']
changed = {m['release'] for m in REG if m['text_changed']}
down = set(changed); st = list(changed)
while st:
    x = st.pop()
    for y in R.rev[x]:
        if y not in down: down.add(y); st.append(y)
def src(m):
    f = H / 'sources' / f'{m}.lean'
    if f.exists(): return f.read_text()
    for p in (f'lean/{m}.lean', f'evidence/replay-dry9-20261027/{m}.lean'):
        r = subprocess.run(['git', '-C', '/Users/dominic/ZK', 'show', f'research:{p}'], capture_output=True)
        if r.returncode == 0: return r.stdout.decode()
    return None
_imps = {}
def imps(m):
    if m not in _imps:
        s = src(m); _imps[m] = [l[7:].strip() for l in s.split('\n') if l.startswith('import ')] if s else R.imp.get(m, [])
    return _imps[m]
def plan():
    order = []; seen = set()
    def visit(m):
        if m in seen or m not in down: return
        seen.add(m)
        for d in imps(m): visit(d)
        order.append(m)
    for m in sorted(down): visit(m)
    ready, blocked = [], {}
    for m in order:
        bad = [d for d in imps(m) if not ((d in down and d in ready) or (d not in down and R.ok(d)))]
        (blocked.__setitem__(m, bad) if bad else ready.append(m))
    return ready, blocked
if __name__ == '__main__':
    ready, blocked = plan()
    inc = lambda m: m in R.imp
    print(json.dumps(dict(changed=len(changed), nodes=len(down), ready=len(ready), ready_in_closure=sum(map(inc, ready)), blocked=len(blocked)), indent=1))
    roots = collections.Counter(d for v in blocked.values() for d in v if d not in down)
    print('non-W5 blockers (count of W5 nodes blocked directly):', roots.most_common(12))
    (H / 'PLAN.json').write_text(json.dumps(dict(ready=ready, blocked=blocked), indent=1) + '\n')
    print(' '.join(ready))
