"""Derive review-only statuses; never mutate the authoritative ledgers."""
from NEH_scan import *
A=read_json(E/'NEH_APPLICABILITY.json');by={r['receipt']:r for r in A['receipts']};runs={}
for q in sorted(E.glob('NEH_K*/receipt.json')):
 r=read_json(q);rp=r.get('deps_fingerprint',{}).get('original_receipt')
 if not rp:continue
 t=(q.parent/'stdout.log').read_text();v='PASS' if 'VERIFICATION:- SUCCESSFUL' in t else 'FAIL' if 'VERIFICATION:- FAILED' in t else 'OPEN'
 runs.setdefault(rp,[]).append(dict(attempt=r['attempt'],verdict=v,exit=r['exit_status'],wall=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],receipt=str(q.relative_to(ROOT))))
# Exact known pairs, including negative controls with the same harness name.
pairs=[]
ndh=read_json(E/'NEH_PRIORITY_NDH.json');ss=sorted(r['receipt'] for r in ndh)
for i in range(0,len(ss),2):pairs.append((ss[i],ss[i+1]))
nec=read_json(ROOT/'evidence/slice-s-leaves-20261029/NEC_CLOSED.json')
for c in nec:pairs.extend(zip(c['kani_receipt_paths'],c['control_receipts']))
extra=E/'NEH_EXTRA_PAIRS.json'
if extra.exists():pairs.extend(read_json(extra))
cleared={};withdrawn={};partial={}
for p,c in pairs:
 if p not in runs or c not in runs:continue
 a=runs[p][-1];b=runs[c][-1]
 # A raw direct check does not replace a historical proof_for_contract for composition.
 method=E/(f'NEH_{Path(p).parent.name}_migration.json')
 direct=method.exists() and read_json(method)['method'].startswith('direct')
 if a['verdict']=='PASS' and b['verdict']=='FAIL':
  for rp in [p,c]:
   (partial if direct else cleared)[rp]=dict(positive=a['attempt'],control=b['attempt'])
 elif a['verdict']=='FAIL' or b['verdict']=='PASS':
  for rp in [p,c]:withdrawn[rp]=dict(positive=a['attempt'],control=b['attempt'])
rows=[]
for rp,r in by.items():
 if rp in withdrawn:state='WITHDRAWN';reason='native property failed or matched control passed'
 elif rp in cleared:state='RESTORED';reason='same property and names, static-free local/owned context, positive PASS and matched control FAIL'
 elif rp in partial:state='OPEN';reason='local native selected value/frame restored; historical function-contract composition certificate still needs explicit local-index transport'
 elif r['classification']=='UNAFFECTED':state='UNAFFECTED';reason='no exposure in recovered receipt-pinned inputs; independent quarantine and source-closure qualifications retained'
 else:state='OPEN';reason='SUSPENDED: '+','.join(r['reason'])
 rows.append(dict(receipt=rp,harness=r['harness'],groups=r['groups'],claims=r['claims'],dependent_rows=r['rows'],outcome=state,reason=reason,runs=runs.get(rp,[]),pair=cleared.get(rp,withdrawn.get(rp,partial.get(rp)))))
# This records direct selected-support consequences. Never infer a whole composition
# closure from the absence of a direct receipt; callee/native/source trust remains.
index=collections.defaultdict(list)
for r in rows:
 for key in r['dependent_rows']:index[key].append(r)
result=[]
for group,path in [('NDT',ROOT/'evidence/native-ledger3-20261029/NDT_LEDGER.json'),('NEB',ROOT/'evidence/slice-q-compose-20261029/NEB_LEDGER.json.xz')]:
 d=read_json(path)
 for r in d['rows']:
  if group=='NEB' and r.get('composed_status')!='CLOSED':continue
  key=group+':'+r['row'];s=index.get(key,[]);exposed=[q for q in s if by[q['receipt']]['classification']=='AFFECTED']
  state='WITHDRAWN' if any(q['outcome']=='WITHDRAWN' for q in s) else 'SUSPENDED' if any(q['outcome']=='OPEN' for q in s) else 'RESTORED' if exposed else 'UNAFFECTED_DIRECT_SUPPORT'
  result.append(dict(row=key,function=r['function'],previous_status=r.get('composed_status',r.get('bridge_status')),k3_direct_support_status=state,affected_receipts=[q['receipt'] for q in exposed],still_suspended=[q['receipt'] for q in s if q['outcome']=='OPEN'],withdrawn_receipts=[q['receipt'] for q in s if q['outcome']=='WITHDRAWN'],limitation='direct selected support only; no automatic adoption or transitive/native root closure'))
for c in nec:
 s=[q for q in rows if c['claim_id'] in q['claims']];result.append(dict(row=c['claim_id'],k3_direct_support_status='WITHDRAWN' if any(q['outcome']=='WITHDRAWN' for q in s) else 'SUSPENDED' if any(q['outcome']=='OPEN' for q in s) else 'RESTORED',still_suspended=[q['receipt'] for q in s if q['outcome']=='OPEN']))
out=dict(schema='NEH-ledger-delta-v1',frozen_revision=FROZEN,authoritative_ledger_modified=False,scope='K-3 direct selected support consequences; no transitive or headline closure claim',receipt_counts=dict(collections.Counter(r['outcome'] for r in rows)),receipts=rows,rows=result)
(E/'NEH_LEDGER_DELTA.json').write_text(json.dumps(out,indent=2)+'\n')
lines=['# K-3 harness reruns','','One row per original receipt/harness. RESTORED concerns K-3 only; all original scope, P6/D188 transport trust and K-2 quarantine remain. OPEN includes unattempted or unresolved static-free migration; it is never a pass. Same-name negative controls are identified by their receipt, not a renamed harness.','','| Original receipt | Harness | Outcome | Attempts | Reason |','|---|---|---|---|---|']
for r in rows:lines.append('| '+ ' | '.join([r['receipt'],r['harness'] or 'unresolved',r['outcome'],','.join(q['attempt']+':'+q['verdict'] for q in r['runs']) or 'not submitted',r['reason']])+' |')
(E/'NEH_RERUNS.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(out['receipt_counts']))
