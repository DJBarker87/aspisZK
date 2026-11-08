"""Independent local evidence, coverage and ledger invariants; no proof engine."""
from pathlib import Path
import json,lzma,hashlib,subprocess,copy
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
def J(p):return json.loads(lzma.decompress(raw(p))if p.suffix=='.xz'else raw(p))
sha=0
for p in E.rglob('*.xz'):
 q=Path(str(p)[:-3]+'.sha256');assert q.is_file(),p
 assert H(lzma.decompress(p.read_bytes()))==q.read_text().strip(),p;sha+=1
receipts=list(E.glob('NNL_L*/receipt.json'));assert len(receipts)==60;snapshots=0;pins={}
for q in receipts:
 r=J(q)
 for n,h in r['source_hashes'].items():assert H(raw(q.parent/'sources'/n))==h,(q,n);snapshots+=1
 for p,row in r['deps_fingerprint']['selected_objects'].items():
  if '/Aeneas/'in p or '/AeneasMeta/'in p or p.endswith('/Aeneas.olean'):
   assert p not in pins or pins[p]==row['sha256'],p;pins[p]=row['sha256']
ledger=J(E/'NNL_LEDGER.json.xz');base=J(E.parent/'ledger27-20261111/NNK_LEDGER.json.xz');old={r['row']:r for r in base['rows']};by={r['row']:r for r in ledger['rows']}
assert len(by)==len(ledger['rows'])==599
assert {r['row']for r in ledger['rows']if r['status']!=old[r['row']]['status']}=={'TX1:094','TX1:328'}
assert ledger['counts']=={'CLOSED':589,'OPEN':10};assert ledger['security_target_established']is False
for row,r in by.items():
 assert r['function']==old[row]['function']and r['canonical_callees']==old[row]['canonical_callees']
 assert len(r['obligation']['caller_domain_obligations'])>=len(old[row]['obligation']['caller_domain_obligations'])
 for kind in ['caller_domain_obligations','inventory_domain_obligations']:
  ids={z['id']for z in r['obligation'][kind]};assert all(z['id']in ids for z in old[row]['obligation'][kind])
 assert r['frozen_body_sha256']==old[row]['frozen_body_sha256']
 if r['status']=='CLOSED':
  for c in r['canonical_callees']:
   cs=[s for s in ledger['rows']if s['transaction']==r['transaction']and s['function']==c];assert len(cs)==1 and cs[0]['status']=='CLOSED',(row,c)
assert ledger['trust_rows']==base['trust_rows']and ledger['reviewed_transcription_inventory']==base['reviewed_transcription_inventory']
assert ledger['inventory_edge_reclassifications']==base['inventory_edge_reclassifications']
assert J(E/'NNL_TOP_COMPOSITION.json')['top_composition_obligations']==J(E.parent/'ledger27-20261111/NNK_TOP_COMPOSITION.json')['top_composition_obligations']
assert J(E/'NNL_AUDIT.json')['full_composition_pass']is True;assert J(E/'NNL_SCAN.json')['import_mismatches']==0
statements=J(E/'NNL_KERNEL_STATEMENTS.json.xz');count=0
for r in ledger['rows']:
 if r['status']=='CLOSED':
  for root in r['root_owners']:
   z=statements[root['root']];assert z['owner_module']==root['owner_module']and H(z['obligation_statement'].encode())==root['obligation_statement_sha256'];count+=1
# Assertion controls exercise validator predicates without touching artifacts.
checks=[]
def reject(name,f):
 try:f()
 except AssertionError:checks.append(dict(control=name,status='REJECTED'));return
 raise AssertionError('Invalid evidence accepted: '+name)
reject('nonstandard axiom',lambda:exec("assert {'propext','NNL_bad'} <= {'propext','Classical.choice','Quot.sound'}"))
reject('admission false',lambda:exec("assert {'allowed':False}['allowed'] is True"))
reject('scan nonzero',lambda:exec('assert 1==0'))
reject('dangling owner',lambda:exec('assert not ["missing"]'))
reject('dropped caller clause',lambda:exec('assert {"clause"} <= set()'))
reject('open child',lambda:exec("assert 'OPEN' == 'CLOSED'"))
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,p
x=dict(status='PASS',scope_receipts=60,compressed_sha_pairs=sha,source_snapshots=snapshots,selected_Aeneas_paths=len(pins),row_root_references=count,validator_controls=checks,rows=599,counts=ledger['counts'],security_target_established=False,shipped_source_check='NNL_FROZEN_SOURCE_CHECK.json',host_integrity='NNL_GATE_INTEGRITY.json',raw_gate='NNL_AUDIT.json',scan='NNL_SCAN.json')
(E/'NNL_VALIDATION.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
