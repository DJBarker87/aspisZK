"""Independent coverage/receipt gate, without replaying any theorem."""
from pathlib import Path
import json,hashlib,os
B=Path.cwd();J=lambda p:json.loads(p.read_text());H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=J(B/'NNK_AUDIT_ROOTS.json');groups=manifest['groups'];seen=[];findings=[]
for i,expected in enumerate(groups):
 d=J(B/'NNK_audit'/('split41a'if i==41 else'repair-window48'if i==48 else'repair-window50'if i==50 else'window'+str(i)if i>=42 else'batch'+str(i))/('proof'+str(i)+'.json'))
 assert [r['root']for r in d['results']]==expected
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
  if not r['equal']:assert r['root']in {'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition','LIB_VCarriers.Acc','NNI_CollectorAcc.alias_identity'};findings.append(r['root'])
 seen+=expected
assert len(seen)==len(set(seen))==len(manifest['roots'])==12987
assert set(seen)==set(manifest['roots'])
fx=J(B/'NNK_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==J(B/'NNK_PREVIOUS_FIXTURES.json')['results']and len(fx['results'])==8
assert H(B/'NNK_native/NNK_ProofDriver')==J(B/'NNK_EXPECTED_RAW_BINARY.json')['sha256']
assert J(B/'NNK_audit/all-close/scan.json')['exit_status']==0
for l in(B/'NNK_LOADED_scan.jsonl').read_text().splitlines():
 r=json.loads(l);assert not r['dangling']and not r['duplicate_owners']and r['imports_match']
owners={}
for l in(B/'NNK_L058/stdout.log').read_text().splitlines():
 if 'NNK_OWNER 'in l:
  r=json.loads(l.split('NNK_OWNER ',1)[1]);assert r['root']not in owners;owners[r['root']]=r
assert set(owners)==set(manifest['roots'])
reviews=J(B/'NNK_CANDIDATE_REVIEW.json')['candidates'];assert {r['row']for r in reviews}=={'TX1:137','TX1:087','TX2:217','TX2:234'}
for r in reviews:assert r['remaining_parameters']==[]and owners[r['candidate']]['owner_module']==r['owner']and r['status']=='STATIC_REVIEW_PASS_GATE_PENDING'
assert J(B/'NNK_SYNTAX_ASSOCIATION.json')['status']=='PASS'
native=J(B/'NNK_NNJ_VALIDATION.json');assert len([r for r in native['results']if r['status']=='validated'])==13 and len([r for r in native['results']if r['status']!='validated'])==3
receipts=[]
for p in B.glob('NNK_L[0-9][0-9][0-9]/receipt.json'):
 r=J(p);ad=J(B/(r['attempt']+'-reservation.json'));assert ad['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and str(r['swaps'])=='0'
 assert r['kind']in ['lean','audit','link']
 for name,digest in r['source_hashes'].items():assert H(p.parent/'sources'/name)==digest
 receipts.append(r['attempt'])
assert len(receipts)==59,(len(receipts),receipts)
assert J(B/'NNK_PREDECESSOR_COMPARISON.json')['status']=='PASS'
x=dict(status='PASS',roots=len(seen),groups=len(groups),fixtures=8,collector_findings=findings,exact_owners=len(owners),candidate_rows=[r['row']for r in reviews],completed_prior_receipts=len(receipts),new_kani=0,new_extraction=0,headline_established=False)
p=B/'NNK_audit/all-close/NNK_GATE_INTEGRITY.json';p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
