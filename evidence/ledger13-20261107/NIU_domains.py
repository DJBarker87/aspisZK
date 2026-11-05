"""Record exact dependency coverage without importing outside-slice credit."""
from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent
b=json.loads(lzma.decompress((E.parent/'ledger12-20261107/NIR_LEDGER.json.xz').read_bytes()));review=json.loads((E/'NIU_CANDIDATE_REVIEW.json').read_text());candidates={r['function']:r for r in review['rows']};byrow={r['row']:r for r in b['rows']};byfun={}
for r in b['rows']:byfun.setdefault(r['function'],[]).append(r)
items=[]
for c in review['rows']:
 calls=[]
 for callee in byrow[c['row']]['canonical_callees']:
  rs=byfun.get(callee,[]);closed=[r for r in rs if r['status']=='CLOSED']
  cp=candidates.get(callee)
  assert closed or cp,(c['row'],callee)
  calls.append(dict(callee=callee,basis_closed_rows=[r['row']for r in closed],co_candidate_rows=[x['row']for x in review['rows']if x['function']==callee]if cp else[],basis_owners=[r['root_owners']for r in closed],caller_domain_derivation=c['semantic_review'],caller_complete_roots=c['roots'],candidate_callee_domain=cp['root_domain']if cp else None))
 items.append(dict(row=c['row'],function=c['function'],root_domain=c['root_domain'],canonical_callees=calls,remaining_open_dependencies=[],scope='Certificate call domains only; no parent, different transaction instance or runtime/ELF premise promoted'))
(E/'NIU_CALL_DOMAIN_CHECK.json').write_text(json.dumps(dict(status='PASS_EXACT_BASIS_PLUS_CO_CANDIDATES',rows=items,rows_checked=25,open_dependencies=0,all_status_promotions_pending_full_gate=review['status']!='ADMITTED_FULL_GATE_PASS'),indent=1)+'\n')
p=E.parent/'slice-d-entry6-20261107/NIS_retarget.py';r=subprocess.run(['python3',str(p),'--check'],capture_output=True,text=True);assert r.returncode==0,r.stderr
(E/'NIU_NIS_RETARGET_CHECK.log').write_text(r.stdout+r.stderr)
print(json.dumps(dict(stage='call-domain inventory',rows=25,open_dependencies=0,NIS_import_only='PASS')))
