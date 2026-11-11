# usage: python3 -I mine_only.py <imports.tsv> <deps_R0P.Core.txt> <allowed-built list file> <changed roots...>
# Modules that must be rebuilt (in the R0P.Core cone or depending on a changed root) and all of whose
# transitive imports are either unaffected, in the allowed-built list (W2's + W3b's objects), or in this set.
import sys
imp = {}
for line in open(sys.argv[1]):
    m, _, deps = line.rstrip('\n').partition('\t')
    imp[m[:-6].replace('/', '.')] = [d for d in deps.split(',') if d and d != 'Init']
dep = set(l.strip() for l in open(sys.argv[2])); dep.add('R0P.Core')
allowed = set(l.strip() for l in open(sys.argv[3]) if l.strip())
roots = set(sys.argv[4:]); memo = {}
def affected(m):
    if m in memo: return memo[m]
    memo[m] = False
    memo[m] = m in dep or m in roots or any(affected(d) for d in imp.get(m, []))
    return memo[m]
ok = {}
def good(m):  # every affected import is allowed or itself good
    if m in ok: return ok[m]
    ok[m] = False
    ok[m] = all((not affected(d)) or d in allowed or good(d) for d in imp.get(m, []))
    return ok[m]
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in imp.get(m, []): visit(d)
    if affected(m) and m not in allowed and good(m): order.append(m)
for m in sorted(imp): visit(m)
print('\n'.join(order))
