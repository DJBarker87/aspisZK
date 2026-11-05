"""Seal candidate-to-basis obligations, never promote before the full gate."""
from pathlib import Path
import json,lzma,hashlib,re,collections
E=Path(__file__).resolve().parent
J=lambda p:json.loads(p.read_text())
H=lambda raw:hashlib.sha256(raw).hexdigest()
b=json.loads(lzma.decompress((E.parent/'ledger12-20261107/NIR_LEDGER.json.xz').read_bytes()));by={r['row']:r for r in b['rows']}
owners={}
for l in (E/'NIU_L003/stdout.log').read_text().splitlines():
 if l.startswith('NIU_OWNER '):
  x=json.loads(l[len('NIU_OWNER '):]);owners[x['root']]=x
assert len(owners)==len(J(E/'NIU_AUDIT_ROOTS.json')['roots'])
nis=J(E.parent/'slice-d-entry6-20261107/NIS_CLOSED.json');nih=J(E.parent/'verify-observed4-20261107/NIH_CLOSED.json')
nsdelta=J(E.parent/'slice-d-entry6-20261107/NIS_LEDGER_DELTA.json');nsby={x['row']:x for x in nsdelta['rows']}
rows=[]
for provider,fs in [('NIS',nis['functions']),('NIH',nih['functions'])]:
 for f in fs:
  function=f.get('subject',f.get('function'))
  ids=f.get('rows',[r for r in nsby if by[r]['function']==function])
  roots=f.get('lean_roots',[f.get('model_theorem')]);assert all(n in owners for n in roots),(provider,roots)
  for rid in ids:
   old=by[rid];assert old['status']=='OPEN',(rid,'double count')
   assert old['function']==function
   if provider=='NIS':
    assert nsby[rid]['frozen_body_sha256']==old['frozen_body_sha256']
   statement_hashes=[dict(root=n,owner_module=owners[n]['owner_module'],statement_sha256=H(owners[n]['obligation_statement'].encode()))for n in roots]
   if provider=='NIS':assert all(x['owner_module'].startswith('NIS_')for x in statement_hashes)
   else:assert all(x['owner_module'].startswith('NIH_')for x in statement_hashes)
   clauses=[]
   for category in ['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']:
    for i,c in enumerate(old['obligation'].get(category,[])):
     clauses.append(dict(category=category,index=i,original=c,disposition='retained interpretation/trust qualification'if category=='named_hypotheses'and 'PhysicalInterpretation'in c.get('name','')else'candidate root domain and complete same-input packet; see row review',certificate_roots=roots))
   rows.append(dict(row=rid,provider=provider,function=function,previous_status=old['status'],basis_obligation_statement_hash=old['obligation_statement_hash'],frozen_body_sha256=old['frozen_body_sha256'],root_domain=f['root_domain'],certificate=f,roots=statement_hashes,complete_kernel_statements=[owners[n]for n in roots],basis_clauses=clauses,review='PENDING full gate and semantic row review',new_credit=True))
assert len(rows)==25 and len({r['row']for r in rows})==25
(E/'NIU_CANDIDATE_REVIEW.json').write_text(json.dumps(dict(status='SEALED_PENDING_GATE',rows=rows,corrected_import=dict(row='TX1:147',previous_status=by['TX1:147']['status'],new_credit=False,reason='NIH corrected import only; retain NIR canonical certificate'),no_double_count=True),indent=1)+'\n')
# Every inherited selected root is checked on the combined environment; changed owners are findings.
oldroots={x['root']:x for r in b['rows']for x in r['root_owners']};checks=[]
for n,x in oldroots.items():
 assert n in owners,n
 actual=owners[n];assert actual['owner_module']==x['owner_module'],(n,x['owner_module'],actual['owner_module'])
 assert H(actual['obligation_statement'].encode())==x['obligation_statement_sha256'],n
 checks.append(dict(root=n,owner_module=actual['owner_module'],statement_sha256=x['obligation_statement_sha256']))
(E/'NIU_OWNER_CHECK.json').write_text(json.dumps(dict(status='PASS_KERNEL_OWNER_STATEMENTS',roots=len(owners),inherited_row_roots=len(checks),candidate_rows=len(rows),inherited_checks=checks,new_checks=[x for r in rows for x in r['roots']],scan='PENDING',duplicate_owners='PENDING whole-import scan'),indent=1)+'\n')
print(json.dumps(dict(stage='candidate-review',rows=len(rows),roots=len(owners),inherited_roots=len(checks),double_count=0)))
