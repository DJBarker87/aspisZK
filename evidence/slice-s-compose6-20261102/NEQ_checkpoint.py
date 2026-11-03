"""Refresh only lane evidence; no closure inferred from a model theorem alone."""
from pathlib import Path
import json,hashlib,collections,subprocess,datetime
import NEQ_validate as v
E=Path(__file__).resolve().parent;R=E.parent.parent
b=v.read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');p=v.read(E/'NEQ_LEDGER_DELTA.json');review=v.read(E/'NEQ_REVIEWED_CERTIFICATES.json');summary=v.read(E/'NEQ_DECODE_VALIDATION.json');spec=v.read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S'];closed=set(summary['slice_closed'])
by={f:[r for r in b['rows'] if r['function']==f] for f in spec['functions']}
old=v.read(E.parent/'slice-s-compose5-20261102/NEM_EDGES.json');prior={x['edge']:x for x in old['edges']};edges=[]
for key in spec['internal_edges']:
 f,g=key.split(' -> ');c=p['edges'].get(key);valid=v.certificate(c,key,b,review) if c else False
 e=dict(prior[key]);e.update(status='CLOSED' if valid else 'OPEN',classification=c['kind'] if valid else e['classification'],certificate_id=c['id'] if valid else None,certificate=dict(overlay='NEQ_LEDGER_DELTA.json',group='edges',subject=key,sha256=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest(),theorems=[t['name'] for t in c['theorems']],native_receipts=c['native_association']) if valid else None,callee_composed=all(r['row'] in closed for r in by[g]),caller_composed=all(r['row'] in closed for r in by[f]),exact_obstacle=None if valid else e['exact_obstacle']);edges.append(e)
assert len(edges)==129
(E/'NEQ_EDGES.json').write_text(json.dumps(dict(slice='S',frozen_revision=b['frozen_revision'],edges=edges,counts=dict(collections.Counter(x['status'] for x in edges))),indent=1)+'\n')
(E/'NEQ_PROGRESS.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),closed_rows=len(closed),roots=summary['roots'],kani_used=len(list(E.glob('NEQ_K*/receipt.json'))),lean_used=len(list(E.glob('NEQ_L*/receipt.json'))),kani_budget=120,lean_budget=80,target_established=False,trust='P6/D188 option A reclassification; approved runtime trust and RuntimePersistence retained'),indent=1)+'\n')
print(json.dumps(dict(closed_rows=len(closed),edges=dict(collections.Counter(x['status'] for x in edges)))))
