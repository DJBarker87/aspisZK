from pathlib import Path
import json,lzma,hashlib,copy
E=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes())
b=J(E.parent/'ledger14-20261108/NJK_LEDGER.json.xz');by={r['row']:r for r in b['rows']}
packets={p['row']:p for p in J(E.parent/'multiproof2-20261107/NJE_ROW_PACKETS.json')}
rows=[];parent=[]
for folder,pre in [('multiproof2-20261107','NJE'),('terminal-20261107','NJB')]:
 for f in J(E.parent/folder/f'{pre}_CLOSED.json')['functions']:
  for rid in f['rows']:
   r=by[rid];assert r['status']=='OPEN' and r['function']==f['function'],rid
   if f.get('frozen_body_sha256'):assert f['frozen_body_sha256']==r['frozen_body_sha256']
   p=packets.get(rid);checks=[]
   if p:
    assert p['function']==r['function'] and p['frozen_body_sha256']==r['frozen_body_sha256'] and p['obligation_statement_hash']==r['obligation_statement_hash'],rid
    for key,pk in [('inventory_domain_obligations','inventory'),('caller_domain_obligations','caller_clauses')]:
     actual=[v['original'] for v in p[pk]];assert actual==r['obligation'][key],(rid,key)
     checks.append(dict(category=key,all_original_clauses_identical=True,count=len(actual)))
    inv=p['aq2_hypothesis_inventory'];assert not inv.get('extra_logical_hypotheses') and not inv.get('endpoint_or_success_premises')
   else:
    inv=dict(root_inputs='every typed statement, both variants; no logical hypothesis',headline_hypotheses=[],reviewed_parent_cuts=[],extra_logical_hypotheses=[],endpoint_or_success_premises=[])
   for c in r['obligation']['inventory_domain_obligations']:
    if p and c['unit'] in ['multiproof','U09']:
     par='TX1:127' if rid.startswith('TX1:') else 'TX2:093'
     # Occurrence-specific unit obligations must be visible at the actual OPEN parent.
     assert by[par]['status']=='OPEN'
     parent.append(dict(parent=par,helper=rid,original=copy.deepcopy(c),caller_clause=dict(id=f'NJO-unit-caller:{par}:{rid}',caller=by[par]['function'],callee=r['function'],required=c['domain'],unit=c['unit'],status='OPEN',discharged_by=None,reason='Retained verbatim at verify_in_place; helper owns only its own carrier. No parent promotion.')))
   rows.append(dict(row=rid,provider=pre,function=r['function'],basis_obligation_statement_hash=r['obligation_statement_hash'],frozen_body_sha256=r['frozen_body_sha256'],certificate=f,root_domain=f['root_domain'],roots=f['lean_roots'],original_clauses={k:r['obligation'][k]for k in ['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']},packet=p,checks=checks,hypothesis_inventory=inv,admissible_pending_gate=True,review='Complete own-carrier Result/post/frame packet; original unit/upstream caller clauses retained. Reviewed native cuts only; internal callee laws installed at SAME arguments. Existing runtime digest value is quantified, not evaluated. Native/compiler/ABI/library/source-to-ELF transport retained as P6/D188 reclassification.'))
assert len(rows)==len({r['row']for r in rows})==25
(E/'NJO_CANDIDATE_REVIEW.json').write_text(json.dumps(dict(status='PENDING_KERNEL_STATEMENTS_AND_FULL_GATE',rows=rows,no_double_count=True),indent=1)+'\n')
(E/'NJO_PARENT_CLAUSES.json').write_text(json.dumps(dict(status='OPEN_PARENT_CALLER_OBLIGATIONS_RETAINED',clauses=parent,parents=['TX1:127','TX2:093'],no_parent_promotion=True),indent=1)+'\n')
print(json.dumps(dict(candidates=len(rows),explicit_parent_clauses=len(parent),pending_gate=True)))
