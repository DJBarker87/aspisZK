#!/usr/bin/env python3
"""jstatus.py MANIFEST ROOT  -- read-only: joint-drive.py's stale() test for ROOT's manifest closure in env J."""
import sys, json, os
J = '/home/dombarker/project-offloads/aspis-joint-20261019'
man = json.load(open(sys.argv[1])); mods = {e['module']: e for e in man['order']}
green, gat = {}, {}
for l in open(f'{J}/evidence/attempts.jsonl'):
    r = json.loads(l)
    if r.get('exit') == 0: green[r['module']] = r['source_sha256']; gat[r['module']] = r['attempt']
def stale(m):
    e = mods[m]
    if green.get(m) != e['sha256']: return True
    return any(x in mods and gat.get(x, 10**9) > gat[m] for x in e['imports'])
seen, st = set(), [sys.argv[2]]
while st:
    m = st.pop()
    if m in seen or m not in mods: continue
    seen.add(m); st.extend(mods[m]['imports'])
order = [e['module'] for e in man['order'] if e['module'] in seen]
S = [m for m in order if stale(m)]
print(f'{sys.argv[2]}: {len(order)} manifest modules in closure, {len(S)} stale')
for m in S: print('  stale', m, 'green_at', gat.get(m), 'sha_match', green.get(m) == mods[m]['sha256'])
# transitive: everything in the closure downstream of a stale module must be rebuilt too
bad = set(S)
for m in order:
    if any(x in bad for x in mods[m]['imports']): bad.add(m)
R = [m for m in order if m in bad]
print(f'rebuild set (stale + downstream, in order): {len(R)}')
for m in R: print('  ', m, 'green_at', gat.get(m))
