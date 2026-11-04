#!/usr/bin/env python3
"""Prefix-owned copy of NFQ_build.py closure core; source provenance pinned in NGB_OVERLAY.
Slice definition: exact canonical-callee closure, same VERTICAL-SLICES schema.
No discovery-mention edges and no evidence/status promotion.
"""
import collections, hashlib, json, lzma, pathlib, subprocess
E=pathlib.Path(__file__).resolve().parent; R=E.parents[1]
LP='evidence/inv-repair-20261104/NGB_ADMITTED_LEDGER.json.xz'
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
put('NGB_SLICE_D.json',dict(source=LP,frozen_revision=L['frozen_revision'],slices={'D':sl}))
put('NGB_SLICES.json',dict(source=LP,frozen_revision=L['frozen_revision'],slices={**{name:{**S['slices'][name], 'functions':sorted(fs)} for name,fs in regenerated.items()},'D':sl}))
coverage=[]
for r in rows:
 memberships=[s for s in ['Q','S'] if r['function'] in regenerated[s]]+(['D'] if r['function'] in D else [])
 coverage.append(dict(row=r['row'],transaction=r['transaction'],function=r['function'],slices=memberships,status=r['composed_status'],frozen_call_path=paths[r['transaction']].get(r['function']),canonical_union_path=global_paths.get(r['function']),reason=None if memberships else ('Canonical graph omits map_err(error) callback edge. Frozen first_decoded calls map_err(error); callback is not a direct-call target in the inventory.' if r['function'].endswith('lib.rs::error') else 'No incoming path in the canonical union. Trait CodeField::from_m31 dispatch is not resolved to this inventory node; absence is a graph gap, not proof of non-reachability.')))

put('NGB_COVERAGE.json',dict(frozen_revision=L['frozen_revision'],counts=dict(total=len(rows),covered=sum(bool(r['slices']) for r in coverage),outside=sum(not r['slices'] for r in coverage),D_functions=len(D),D_edges=len(edges),D_rows=len(dr)),rows=coverage,authority='NFZ canonical-union closure core with NGB reviewed additive edges and explicit OPEN occurrences; canonical coverage is not native closure'))
print(json.dumps(dict(rows=len(rows),covered=sum(bool(r['slices']) for r in coverage),outside=[r['row'] for r in coverage if not r['slices']])))

# Explicitly replace historical exact-Q equality with before/after memberships.
before=json.loads((R/'evidence/inv-defects-20261104/NFZ_SLICES.json').read_text())['slices']
changes={}
for name in ['Q','S','D']:
 old=set(before[name]['functions']);new=set(D if name=='D' else regenerated[name])
 changes[name]=dict(before_functions=len(old),after_functions=len(new),added=sorted(new-old),removed=sorted(old-new),before_membership=sorted(old),after_membership=sorted(new))
base=json.loads(lzma.open(R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz').read())
status=lambda rs:dict(collections.Counter(r['composed_status'] for r in rs))
oldix={r['row']:r for r in base['rows']}
assert all(r['composed_status']==oldix[r['row']]['composed_status'] for r in rows if r['row'] in oldix)
assert len(coverage)==len(rows) and all(r['slices'] for r in coverage)
newrows=[r for r in rows if r['row'] not in oldix]
assert all(r['composed_status']=='OPEN' for r in newrows)
put('NGB_LEDGER_DELTA.json',dict(basis='NFX_LEDGER.json.xz plus reviewed NGB overlay; all historical NFX summary fields inherited and superseded for repaired counts by this delta',before=dict(rows=len(base['rows']),statuses=status(base['rows']),unique_functions=len({r['function'] for r in base['rows']}),covered=585),after=dict(rows=len(rows),statuses=status(rows),unique_functions=len(graph),covered=len(coverage)),row_delta=len(newrows),new_rows=[dict(row=r['row'],function=r['function'],transaction=r['transaction'],status=r['composed_status']) for r in newrows],removed_rows=[],status_changes=[],closed_promotions=0,slice_membership_changes=changes,per_slice={s:dict(rows=sum(s in c['slices'] for c in coverage),statuses=status([r for r,c in zip(rows,coverage) if s in c['slices']])) for s in ['Q','S','D']},transaction_paths_missing=[c for c in coverage if c['frozen_call_path'] is None]))
(E/'NGB_COVERAGE.md').write_text(f"""# Repaired D union Q union S coverage

{len(coverage)}/{len(rows)} rows covered by the regenerated canonical union; zero outside. Baseline: 585/587. New rows: {len(newrows)}, all OPEN. Historical statuses unchanged; no native closure or security premise discharge is claimed.

The NFZ_slice_build.py closure semantics are retained: per-TX shortest paths; union canonical graph; Q/S root closures; D is entry cone minus Q union S. The old exact-Q membership assertion is replaced by the complete before/after sets in NGB_LEDGER_DELTA.json. Q now includes the WideExact CodeField::from_m31 chain. Shared field embeddings formerly in D move into Q. No row is silently excluded.

NGB_COVERAGE.json records every TX occurrence, slice membership and both per-TX and canonical-union paths. {sum(c['frozen_call_path'] is None for c in coverage)} inherited occurrences still lack a TX-specific path; union membership is dependency coverage, not a proof of physical same-run reachability. NGB_EXCLUDED.json records the audit-only accumulation pair separately.

NFZ_C0032 remains an explicit compiler-evidence gap (statement MIR is empty); no callback edge or reachability exclusion is fabricated. Thus the 39-candidate repair is incomplete even though every current row has slice membership. Native/model callee-naming findings are in NGB_Q_CALLEE_FINDING.md; the lead owns status decisions.
""")
