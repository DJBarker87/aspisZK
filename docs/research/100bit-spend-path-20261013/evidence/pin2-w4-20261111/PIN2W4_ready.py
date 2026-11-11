"""Which data-dependent modules can be compiled coherently now?
A module is ready when every import is (a) in overlay-PIN2-W4, or (b) not
downstream of the fixture data and either in overlay-PIN2 or untouched by
PIN2 (not in PIN2-HOST-REBUILD-ORDER) and present in objs.
usage: python3 -I PIN2W4_ready.py [module ...]   (no args: summary)"""
import sys, os, collections
from pathlib import Path
HERE = Path(__file__).resolve().parent
C = '/Users/dominic/aspis-lead-infra/l187-closure'
imp = {}
for l in open(HERE.parent / 'pin2-public-binding-20261110/impact-scan/imports.tsv'):
    a, b = l.rstrip('\n').split('\t'); imp[a[:-6]] = [x for x in b.split(',') if x and x != 'Init']
rev = collections.defaultdict(set)
for m, ds in imp.items():
    for d in ds: rev[d].add(m)
import json
data = {m['release'] for m in json.loads((HERE / 'REGEN.json').read_text())['modules'] if m['text_changed'] and m['release'].startswith('RPz8_JFx_Data')}
dep = set(data); st = list(data)
while st:
    x = st.pop()
    for y in rev[x]:
        if y not in dep: dep.add(y); st.append(y)
aff = {l.split('\t')[1] for i, l in enumerate(open('/Users/dominic/aspis-lead-infra/PIN2-HOST-REBUILD-ORDER.tsv')) if i}
has = lambda d, m: os.path.isfile(f'{C}/{d}/{m.replace(".", "/")}.olean')
def ok(d):
    if has('overlay-PIN2-W4', d): return True
    if d in dep: return False
    if has('overlay-PIN2', d): return True
    return d not in aff and (has('objs', d) or has('base', d))
def why(m): return [d for d in imp.get(m, []) if not ok(d)]
if __name__ == '__main__':
    if len(sys.argv) > 1:
        for m in sys.argv[1:]: print(m, 'READY' if not why(m) else 'BLOCKED ' + ' '.join(why(m)))
    else:
        todo = [m for m in dep if not has('overlay-PIN2-W4', m)]
        r = [m for m in todo if not why(m)]
        print('data-dependent', len(dep), 'built in W4', len(dep) - len(todo), 'ready now', len(r)); print(' '.join(sorted(r)))
