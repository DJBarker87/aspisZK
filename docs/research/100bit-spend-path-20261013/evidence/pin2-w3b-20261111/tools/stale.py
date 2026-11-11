# usage: python3 -I stale.py <imports.tsv> <deps_R0P.Core.txt> <overlay dir> Module [Module...]
# prints, per target, its transitive imports that depend on R0P.Core and have no overlay object
import sys, os
imp = {}
for line in open(sys.argv[1]):
    m, _, deps = line.rstrip('\n').partition('\t')
    imp[m[:-6].replace('/', '.')] = [d for d in deps.split(',') if d and d != 'Init']
dep = set(l.strip() for l in open(sys.argv[2]))
ov = sys.argv[3]
def built(m): return os.path.exists(os.path.join(ov, m.replace('.', '/') + '.olean'))
for t in sys.argv[4:]:
    seen, stack = set(), list(imp.get(t, []))
    while stack:
        m = stack.pop()
        if m in seen: continue
        seen.add(m); stack.extend(imp.get(m, []))
    stale = sorted(m for m in seen if (m in dep or m == 'R0P.Core') and not built(m))
    # minimal frontier: stale modules none of whose imports are stale
    sset = set(stale)
    front = [m for m in stale if not any(d in sset for d in imp.get(m, []))]
    print(f"{t}: {len(stale)} stale imports; frontier {front[:12]}")
