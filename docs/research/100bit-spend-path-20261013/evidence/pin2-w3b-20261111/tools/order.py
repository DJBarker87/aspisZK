# usage: python3 -I order.py <imports.tsv> <deps_R0P.Core.txt> <overlay> Target...
# prints the stale (R0P.Core-dependent, not yet in overlay) transitive imports of the targets
# plus the targets, in import order; also non-dependent R0P.* imports missing from the overlay
import sys, os
imp = {}
for line in open(sys.argv[1]):
    m, _, deps = line.rstrip('\n').partition('\t')
    imp[m[:-6].replace('/', '.')] = [d for d in deps.split(',') if d and d != 'Init']
dep = set(l.strip() for l in open(sys.argv[2])); dep.add('R0P.Core')
ov = sys.argv[3]
def built(m): return os.path.exists(os.path.join(ov, m.replace('.', '/') + '.olean'))
order, seen, shadow = [], set(), set()
def visit(m, top=False):
    if m in seen: return
    seen.add(m)
    for d in imp.get(m, []): visit(d)
    if top or (m in dep and not built(m)): order.append(m)
    elif m.startswith('R0P.') and not built(m): shadow.add(m)
for t in sys.argv[4:]: visit(t, True)
print('\n'.join(order))
if shadow: print('# non-dependent R0P modules missing from overlay:', ' '.join(sorted(shadow)))
