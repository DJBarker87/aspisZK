"""Effective import graph over LEAN_PATH = overlay-PIN2-W4 : overlay-PIN2 : objs : base.
Imports are read from the object files themselves (Imports.lean, readModuleData),
for whichever layer resolves the module first.  Scans are cached in SCAN (dir).
usage (library): import PIN2W6_graph as G; G.load(scan_dir)"""
import os, collections
C = '/Users/dominic/aspis-lead-infra/l187-closure'
TOOLCHAIN = os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
LAYERS = ['overlay-PIN2-W4', 'overlay-PIN2', 'objs', 'base']
imp = {}; layer = {}
def load(scan):
    for L in LAYERS[:3]:
        for line in open(f'{scan}/imp-{L}.tsv'):
            rel, _, deps = line.rstrip('\n').partition('\t')
            m = rel[:-6].replace('/', '.')
            if m in layer: continue          # earlier layer shadows
            layer[m] = L; imp[m] = [d for d in deps.split(',') if d and d != 'Init']
def path(m):
    L = layer.get(m)
    if L is None:
        for root in (f'{C}/base', TOOLCHAIN):
            p = f'{root}/{m.replace(".", "/")}.olean'
            if os.path.isfile(p): return p
        return None
    return f'{C}/{L}/{m.replace(".", "/")}.olean'
def closure(m):
    seen = set(); st = list(imp.get(m, []))
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x); st.extend(imp.get(x, []))
    return seen
def rev():
    r = collections.defaultdict(set)
    for m, ds in imp.items():
        for d in ds: r[d].add(m)
    return r
