"""Reports derived from the successful final admission summary, no new credit."""
from pathlib import Path
from collections import Counter
import json,hashlib
from NEU_inputs import read
E=Path(__file__).resolve().parent;R=E.parent.parent
summary=read(E/'NEU_DECODER_VALIDATION.json');base=read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');slice=read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S'];packet=read(E/'NEU_LEDGER_DELTA.json');old=read(E/'NEU_EDGES.json');closed=set(summary['slice_closed']);functions=set(slice['functions']);rows=[r for r in base['rows'] if r['function'] in functions];assert len(rows)==97
byfunction={f:[r for r in rows if r['function']==f] for f in functions}
isclosed=lambda f:f in byfunction and all(r['row'] in closed for r in byfunction[f])
blob=(E/'NEU_LEDGER_DELTA.json.sha256').read_text().strip()
for e in old['edges']:
 caller,callee=e['edge'].split(' -> ');e['caller_composed']=isclosed(caller);e['callee_composed']=isclosed(callee)
 cert=packet['edges'].get(e['edge'])
 if cert and cert['id'].startswith('NEU_'):
  assert caller in summary['native_admissions']['verified']
  e.update(status='CLOSED',certificate_id=cert['id'],certificate=dict(overlay='NEU_LEDGER_DELTA.json.xz',uncompressed_sha256=blob,group='edges',subject=e['edge'],sha256=hashlib.sha256(json.dumps(cert,sort_keys=True).encode()).hexdigest(),theorems=[t['name'] for t in cert['theorems']],native_receipts=[r for r in cert['native_association'] if r['path'].endswith('/receipt.json')]),classification='ruling-y full typed Box/Result source packet, indexed field assembly and exact same-call domain')
 if e['status']=='CLOSED' and e.get('exact_obstacle'):
  e['inherited_obstacle_superseded_by_certificate']=e.pop('exact_obstacle')
old['counts']=dict(Counter(e['status'] for e in old['edges']));old['provenance']='NEQ inherited certificates plus four strictly admitted NEU members; current successful validator summary; no support-cut/root promotion'
(E/'NEU_EDGES.json').write_text(json.dumps(old,indent=1)+'\n')
perroot={}
for root in slice['roots']:
 reached=set()
 def visit(f):
  if f in reached or f not in functions:return
  reached.add(f)
  for r in byfunction[f]:
   for g in r['canonical_callees']:visit(g)
 visit(root);rr=[r for f in reached for r in byfunction[f]]
 perroot[root]=dict(root_status='CLOSED' if isclosed(root) else 'OPEN',closed_rows=sum(r['row'] in closed for r in rr),total_rows=len(rr),closed_functions=sum(isclosed(f) for f in reached),total_functions=len(reached),overlap_note='shared descendants count under each reachable root; do not sum these counts')
(E/'NEU_ROOT_COUNTS.json').write_text(json.dumps(dict(total_closed_rows=len(closed),total_rows=97,closed_functions=sum(isclosed(f) for f in functions),total_functions=61,roots=perroot),indent=1)+'\n')
openmembers=[]
for f in sorted(functions):
 if isclosed(f):continue
 rr=byfunction[f];openmembers.append(dict(function=f,rows=[r['row'] for r in rr if r['row'] not in closed],baseline_bridge_status=sorted({r['bridge_status'] for r in rr}),open_internal_edges=[e for e in old['edges'] if e['edge'].startswith(f+' -> ') and e['status']!='CLOSED'],baseline_inner_names=sorted({h['name'] for r in rr for h in r['named_hypotheses']}),baseline_obstacles=sorted({r['no_credit_reason'] for r in rr if isinstance(r['no_credit_reason'],str)})))
(E/'NEU_OPEN_MEMBERS.json').write_text(json.dumps(openmembers,indent=1)+'\n')
print(json.dumps(dict(rows=len(closed),functions=sum(isclosed(f) for f in functions),edges=old['counts'],open_functions=len(openmembers))))
