#!/usr/bin/env python3
"""Prefix-owned copy of NFQ_build.py closure core; source provenance pinned in NFZ_OVERLAY.
Slice definition: exact canonical-callee closure, same VERTICAL-SLICES schema.
No discovery-mention edges and no evidence/status promotion.
"""
import collections, hashlib, json, lzma, pathlib, subprocess
E=pathlib.Path(__file__).resolve().parent; R=E.parents[1]
LP='evidence/inv-defects-20261104/NFZ_ADMITTED_LEDGER.json.xz'
SP='docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json'
raw=lzma.open(R/LP).read(); L=json.loads(raw); S=json.loads((R/SP).read_text())
rows=L['rows']
root='programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction'
paths={}; indexes={}
for tx in ['TX1','TX2']:
 ix={r['function']:r for r in rows if r['transaction']==tx};indexes[tx]=ix
 seen={root:[root]};queue=collections.deque([root])
 while queue:
  f=queue.popleft()
  for c in ix[f]['canonical_callees']:
   if c in ix and c not in seen:seen[c]=seen[f]+[c];queue.append(c)
 paths[tx]=seen
graph=collections.defaultdict(set)
for r in rows:graph[r['function']].update(r['canonical_callees'])
def closure(roots):
 seen={f:[f] for f in roots};queue=collections.deque(roots)
 while queue:
  f=queue.popleft()
  for c in sorted(graph[f]):
   if c in graph and c not in seen:seen[c]=seen[f]+[c];queue.append(c)
 return seen
global_paths=closure([root])
regenerated={name:set(closure(spec['roots'])) for name,spec in S['slices'].items()}
qs=regenerated['Q']|regenerated['S']
cone=set(global_paths); D=cone-qs
edges=sorted({f+ ' -> '+c for r in rows for f in [r['function']] if f in D for c in r['canonical_callees'] if c in D})
dr=[r for r in rows if r['function'] in D]
sl=dict(name='driver spine complement of Q and S (TX1+TX2)',roots=[root],functions=sorted(D),open_functions=sorted({r['function'] for r in dr if r['composed_status']!='CLOSED'}),internal_edges=edges,inventory_rows=[r['row'] for r in dr])
def put(n,o): (E/n).write_text(json.dumps(o,indent=2)+'\n')
put('NFZ_SLICE_D.json',dict(source=LP,frozen_revision=L['frozen_revision'],slices={'D':sl}))
put('NFZ_SLICES.json',dict(source=LP,frozen_revision=L['frozen_revision'],slices={**{name:{**S['slices'][name], 'functions':sorted(fs)} for name,fs in regenerated.items()},'D':sl}))
coverage=[]
for r in rows:
 memberships=[s for s in ['Q','S'] if r['function'] in regenerated[s]]+(['D'] if r['function'] in D else [])
 coverage.append(dict(row=r['row'],transaction=r['transaction'],function=r['function'],slices=memberships,status=r['composed_status'],frozen_call_path=paths[r['transaction']].get(r['function']),canonical_union_path=global_paths.get(r['function']),reason=None if memberships else ('Canonical graph omits map_err(error) callback edge. Frozen first_decoded calls map_err(error); callback is not a direct-call target in the inventory.' if r['function'].endswith('lib.rs::error') else 'No incoming path in the canonical union. Trait CodeField::from_m31 dispatch is not resolved to this inventory node; absence is a graph gap, not proof of non-reachability.')))

put('NFZ_COVERAGE.json',dict(frozen_revision=L['frozen_revision'],counts=dict(total=len(rows),covered=sum(bool(r['slices']) for r in coverage),outside=sum(not r['slices'] for r in coverage),D_functions=len(D),D_edges=len(edges),D_rows=len(dr)),rows=coverage,authority='NFQ canonical-union closure core with regenerated Q/S roots and D complement; no reviewed edge admitted'))
print(json.dumps(dict(rows=len(rows),covered=sum(bool(r['slices']) for r in coverage),outside=[r['row'] for r in coverage if not r['slices']])))
