# usage: python3 -I dependents.py <imports.tsv> <deps_R0P.Core.txt> Root...
# transitive dependents of the roots, in import order, split by R0P.Core dependence
import sys
imp = {}
for line in open(sys.argv[1]):
    m, _, deps = line.rstrip('\n').partition('\t')
    imp[m[:-6].replace('/', '.')] = [d for d in deps.split(',') if d and d != 'Init']
dep = set(l.strip() for l in open(sys.argv[2])); dep.add('R0P.Core')
roots = set(sys.argv[3:]); memo = {}
def hit(m):
    if m in memo: return memo[m]
    memo[m] = False
    memo[m] = m in roots or any(hit(d) for d in imp.get(m, []))
    return memo[m]
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in imp.get(m, []): visit(d)
    if hit(m) and m not in roots: order.append(m)
for m in imp: visit(m)
free = [m for m in order if m not in dep]; tied = [m for m in order if m in dep]
print(f"# {len(order)} dependents; {len(free)} independent of R0P.Core, {len(tied)} also under R0P.Core")
print("FREE", ' '.join(free)); print("TIED", ' '.join(tied[:40]), '...' if len(tied) > 40 else '')
