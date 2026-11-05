"""Reconcile predecessor cone without promoting imported caller domains."""
from pathlib import Path
import json,re,collections,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];P=R/'evidence/verify-observed2-20261106'
rows=json.loads((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_text())['rows']
byfun={r['function']:r for r in rows if r['row'].startswith('TX1:')}
root=next(r for r in rows if r['row']=='TX1:137');dist={root['function']:0};q=collections.deque([root['function']])
while q:
 f=q.popleft()
 for child in byfun.get(f,{}).get('canonical_callees',[]):
  if child not in dist:dist[child]=dist[f]+1;q.append(child)
imports={'TX1:027':'NHH_CLOSED.json QM31::inv','TX1:031':'NHN_CLOSED.json QM31::neg','TX1:032':'NGH_CLOSED.json QM31::square','TX1:034':'NHH_CLOSED.json QM31::try_inv','TX1:056':'NGH_CLOSED.json WideExact::square'}
packets={r:f for f in json.loads((E/'NHU_CLOSED.json').read_text())['functions'] for r in f['rows']}
closed=set(packets)
updates={
 'TX1:130':'NHU_Mark.result/frame/effects + exact frozen/NEF source certificate under(z)(1). Only deployed None. No new caller-edge credit.',
 'TX1:136':'Remaining actual children:129 claims,134 rounds,142 circle_validated,147 decode_k caller/payload domain,256 terminal_qm31; then own complete native cuts, emitted/model association, exact WireError paths and frame/effect composition. Mask076 and mark130 are now closed in their stated domains; SAME finish caller instances remain to be proved. Q inverses/neg/squares are imported closed; no longer boundaries.',
 'TX1:137':'One direct OPEN child: finish136. Then own native staged cuts, same-value domain/frame chain, emitted frozen body equality to adopted VerifyPrefix model, complete Result nominal transport to NHL prepare op9, combined ax2 and NFX admission. NHU_VerifyFrame.source is only the adopted-model cut equation.'}
text=['# NHU verify_observed cone','', 'TX1:137 and prepare op9 remain OPEN. Updates preserve each NHG row; Q inv/neg/square/try_inv are CLOSED imports, not slice boundaries. Final additive admission closes11 NHU rows, including mark130 by source no-op reclassification;79 new raw roots and the13832-module scan pass. Root137, finish136 and prepare op9 remain OPEN. No source-refinement gap becomes a crypto assumption.','', 'Distances below are shortest edges in the supplied NDT conservative canonical call inventory, from root137 to the member. They measure call position, not discharged obligations. The final op9 column adds the required complete-Result nominal/source transport from root137 to the exact NHL hypothesis; that transport remains unproved. An absent inventory path is shown explicitly, never invented.','', '| Row | Status | Member | Hops to137 / op9 | Exact remaining obligation |','|---|---|---|---|---|']
records=[]
for l in (P/'NHG_CONE.md').read_text().splitlines():
 m=re.match(r'\| (TX1:\d+) \| (.*?) \| `(.*?)` \| (.*?) \|$',l)
 if not m:continue
 row,status,fun,remaining=m.groups()
 if row in imports:status='CLOSED (import)';remaining=imports[row]+': retain exact packet/domain and prove caller same-value instance; no automatic edge closure.'
 if row in closed:
  status='CLOSED (z1)' if row=='TX1:130' else 'CLOSED (NHU packet)'
  packet=packets[row]
  remaining=packet['lean_root']+'; '+packet['domain']+'. Complete packet admitted; enclosing caller SAME-value/domain obligations are not automatically closed.'
 remaining=updates.get(row,remaining)
 if row in ['TX1:036','TX1:040','TX1:041','TX1:043','TX1:044']:
  remaining='Retired NGH native shape / dependency stop: NGH_REMAINING.md and NGH_CELL_STOP.json. Existing model/domain/induction/wrapper support complete; no unchanged replay or variant of the stopped accumulator. Missing native cell/small-helper contract; dependent wrappers cannot close.'
 d=dist.get(fun);position=f'{d} / {d+1}' if d is not None else 'inventory gap / OPEN'
 text.append(f'| {row} | {status} | `{fun}` | {position} | {remaining} |')
 records.append(dict(row=row,status=status,function=fun,inventory_distance_to_root=d,inventory_distance_to_op9=None if d is None else d+1,remaining=remaining))
text += ['', 'The complete NHL target is `base.op9 D pub v.semantic hash none = expected.op9 D pub v.semantic hash none`, with both sides `Result (RustResult (Verified H) WireError)` and the SAME v reached by the closed predecessor buffers. No whole-verify success or caller-selected result is permitted. No NHU theorem presently instantiates that law.','']
(E/'NHU_CONE.md').write_text('\n'.join(text));(E/'NHU_CONE.json').write_text(json.dumps(dict(rows=records,root_closed=False,prepare_op9_instantiated=False),indent=1)+'\n')
print(json.dumps(dict(rows=len(records),new_rows=sorted(closed),imported_corrections=list(imports))))
