"""Readiness of the fixture-downstream release modules (W6).
dep = release modules (objs import graph) downstream of the RPz8_JFx_Data*
modules.  An import d of a dep module is satisfied when d is in
overlay-PIN2-W4, or d is not in dep and is either in overlay-PIN2 / overlay-HOST-P1 or not
PIN2-affected (not in PIN2-HOST-REBUILD-ORDER.tsv) and present in objs/base.
A dep module is ready when every import is satisfied or is a ready dep module
earlier in the plan (planned, not yet built).
usage: python3 -I PIN2W6_ready.py <scan_dir> [--fixture-only]"""
import sys, os, json, re, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import PIN2W6_graph as G
scan = sys.argv[1]; G.load(scan)
rel = {}
for l in open(f'{scan}/imp-objs.tsv'):
    a, _, b = l.rstrip('\n').partition('\t'); rel[a[:-6].replace('/', '.')] = [x for x in b.split(',') if x and x != 'Init']
rev = collections.defaultdict(set)
for m, ds in rel.items():
    for d in ds: rev[d].add(m)
data = [m for m in rel if m.startswith('RPz8_JFx_Data')]
dep = set(data); st = list(data)
while st:
    x = st.pop()
    for y in rev[x]:
        if y not in dep: dep.add(y); st.append(y)
aff = {l.split('\t')[1] for i, l in enumerate(open('/Users/dominic/aspis-lead-infra/PIN2-HOST-REBUILD-ORDER.tsv')) if i}
KEEP = {l.split('\t')[0] for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'KEEP-RELEASE.tsv')).read().splitlines()[1:]}
inW4 = lambda m: G.layer.get(m) == 'overlay-PIN2-W4' or m in KEEP
def sat(d):
    if inW4(d): return True
    if d in dep: return False
    if G.layer.get(d) in ('overlay-PIN2', 'overlay-HOST-P1'): return True
    return d not in aff and G.path(d) is not None
import PIN2W6_src as S
_si = {}
def imps(m):
    """Imports of the text that will be compiled (W6/W5/W4 source if any), else the object's."""
    if m not in _si:
        b = None
        if m in dep:
            for f in (S.W6 / 'sources' / f'{m}.lean', S.EV / 'pin2-w5-20261111/sources' / f'{m}.lean', S.EV / 'pin2-w4-20261111/sources' / f'{m}.lean'):
                if f.exists(): b = f.read_text(); break
        _si[m] = [l[7:].strip() for l in b.split('\n') if l.startswith('import ')] if b is not None else (G.imp[m] if inW4(m) else rel.get(m, G.imp.get(m, [])))
    return _si[m]
FIX = re.compile(r'^(NDO_J[A-Z]|RPt_J[A-Z]|RPu_J[A-Z]|RPz8_J[A-Z]|J[A-Z][a-z]_)')
def plan(only=None):
    order, seen = [], set()
    def visit(m):
        if m in seen or m not in dep: return
        seen.add(m)
        for d in imps(m): visit(d)
        order.append(m)
    for m in sorted(dep): visit(m)
    ready, blocked = [], {}
    rs = set()
    for m in order:
        if inW4(m): continue
        bad = [d for d in imps(m) if not (sat(d) or d in rs)]
        if bad: blocked[m] = bad
        else: ready.append(m); rs.add(m)
    return order, ready, blocked
def roots(m, blocked, seen=None):
    seen = set() if seen is None else seen
    if m in seen: return set()
    seen.add(m); out = set()
    for d in blocked.get(m, []):
        if d in blocked: out |= roots(d, blocked, seen)
        elif d in dep and not inW4(d): out.add(d + ' (dep, ready-planned)')
        else: out.add(d)
    return out
if __name__ == '__main__':
    order, ready, blocked = plan()
    fx = lambda m: bool(FIX.match(m))
    print('dep', len(dep), 'fixture-named', sum(map(fx, dep)), 'built in W4', sum(1 for m in dep if inW4(m)))
    print('ready', len(ready), '(fixture', sum(map(fx, ready)), ') blocked', len(blocked), '(fixture', sum(map(fx, blocked)), ')')
    rc = collections.Counter(r for m in blocked for r in roots(m, blocked) if not r.endswith('planned)'))
    print('non-dep root blockers:', rc.most_common(25))
    json.dump(dict(order=order, ready=ready, blocked=blocked), open(f'{scan}/plan.json', 'w'), indent=0)
