"""Packet integrity checks plus deliberate admission-record mutations.

This checks receipt/ledger/source fidelity, not a replacement proof checker.
"""
from pathlib import Path
import copy,hashlib,json,lzma,re,subprocess,shutil
E=Path(__file__).resolve().parent
load=lambda n:json.loads((E/n).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def check(a,c,d,o):
 assert a['status'].startswith('PASS') and not a['security_target_established']
 assert a['headline']==c['headline']=='AspisR1.RPx_Deployed.deployed'
 assert a['gate']['combined']=='NKA_L066' and a['gate']['coherence']=='NKA_L067'
 assert a['raw']['all_equal_collectAxioms'] and a['raw']['roots']==40
 assert set(a['raw']['axioms'])<={'propext','Quot.sound','Classical.choice'}
 assert not a['authoritative_ledger_changed'] and not d['authoritative_ledger_changed']
 assert d['baseline_counts']==dict(CLOSED=484,QUALIFIED=0,OPEN=115,total=599)
 assert d['baseline_sha256']==sha(E.parent/'ledger16-20261108/NJW_LEDGER.json.xz')
 assert {r for f in c['functions'] for r in f['rows']}=={'TX1:069','TX1:129'}
 baseline=load('NKA_BASELINE_ROWS.json')
 for f in c['functions']:
  row=f['rows'][0];b=baseline[row]
  assert f['frozen_body_sha256']==b['frozen_body_sha256']
  assert f['obligation_statement_hash']==b['obligation_statement_hash']
  assert o[row]['canonical_callees_retained']==b['canonical_callees']
  assert [x['original'] for x in o[row]['clauses']]==b['obligation']['caller_domain_obligations']
  assert o[row]['inventory_domain_obligations']==b['obligation']['inventory_domain_obligations']
  assert o[row]['named_hypotheses']==b['obligation']['named_hypotheses']
  for pair in f['native_pairs']:
   assert len(pair)>=2,'missing matched control'
   for i,n in enumerate(pair):
    r=load(n+'/receipt.json');text=(E/n/'stdout.log').read_text()
    assert r['exit_status']==(0 if i==0 else 1)
    assert ('VERIFICATION:- SUCCESSFUL' if i==0 else 'VERIFICATION:- FAILED') in text
    assert load(n+'-graph-check.json')['graph_matches_frozen']
    lock=load(n+'-lock-check.json');assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
    assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_TARGET_DIR'].endswith('/codex-cx-claims2-20261108/NKA_target')
 admission=load('NKA_CHILD_ADMISSION.json');assert admission['gate']=='PASS' and admission['frozen_body_hashes_match_NJT']
 assert all(r['status']=='CLOSED' for r in admission['children'])
 observed=load('NKA_LEDGER17_PROVENANCE.json');blob=(E/'NKA_LEDGER17_OBSERVED.json.xz').read_bytes();assert hashlib.sha256(blob).hexdigest()==observed['compressed_sha256']
 ledger=json.loads(lzma.decompress(blob));assert ledger['gate']=='PASS' and ledger['headline']==a['headline']
 indexed={r['row']:r for r in ledger['rows']}
 for r in admission['children']:
  assert indexed[r['row']]['status']=='CLOSED' and indexed[r['row']]['frozen_body_sha256']==r['frozen_body_sha256']
 assert not load('NKA_RESEARCH_CHECK.json')['terminal256_candidate_seen']
 for n in ['NKA_L066','NKA_L067','NKA_L068','NKA_L069','NKA_L070','NKA_L071','NKA_L072']:
  assert load(n+'/receipt.json')['exit_status']==0
 assert load('NKA_audit_final/scan/scan.json')['policy_pass']
 for n in ['NKA_audit_final/batch0/proof0.json','NKA_audit_final/batch1/proof1.json']:
  x=load(n);assert x['exit_status']==0 and x['policy_pass']
  assert all(r['equal'] and r['walked_axioms']==r['collect_axioms'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in x['results'])
 assert 'Ready storage' in (E/'NKA_HeapCarrier.lean').read_text()
 assert 'AtAllocation (allocate allocator state)' in (E/'NKA_ClaimsRoot.lean').read_text()
 assert sha(E/'NKA_KMX.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 assert load('NKA_FINAL_HOST_VALIDATION.json')['status']=='PASS'
 return True
def main():
 a,c,d,o=[load(n) for n in ['NKA_AUDIT.json','NKA_CLOSED.json','NKA_LEDGER_DELTA.json','NKA_ROW_OBLIGATIONS.json']]
 assert check(a,c,d,o)
 mutants=[]
 def reject(label,index,mutate):
  data=copy.deepcopy([a,c,d,o]);mutate(data[index])
  try:check(*data)
  except AssertionError:mutants.append(dict(case=label,rejected=True));return
  raise AssertionError('admitted mutation '+label)
 reject('nonstandard axiom',0,lambda x:x['raw']['axioms'].append('sorryAx'))
 reject('wrong headline',1,lambda x:x.update(headline='AspisR1.Fake.deployed'))
 reject('missing negative control',1,lambda x:x['functions'][0]['native_pairs'][0].__setitem__(slice(1,None),[]))
 reject('wrong baseline',2,lambda x:x['baseline_counts'].update(CLOSED=486))
 reject('dropped conservative edge',3,lambda x:x['TX1:069']['canonical_callees_retained'].pop())
 reject('missing original caller obligation',3,lambda x:x['TX1:129']['clauses'].pop())
 reject('ungated row136',1,lambda x:x['functions'][0]['rows'].append('TX1:136'))
 reject('axiom comparison omitted',0,lambda x:x['raw'].update(all_equal_collectAxioms=False))
 modules=load('NKA_MODULES.json');assert len(modules)==14
 for m in modules:
  assert sha(E/m['source'])==m['sha256'];r=load(m['attempt']+'/receipt.json')
  assert r['exit_status']==0 and m['sha256'] in r['source_hashes'].values()
  assert all('sorryAx' not in l for l in r['print_axioms'])
 for directory in ['NKA_archives','NKA_archives_final']:
  for p in (E/directory).glob('*.xz'):
   assert hashlib.sha256(lzma.decompress(p.read_bytes())).hexdigest()==p.with_suffix('.sha256').read_text().strip()
 for n in ['NKA_FROZEN_PAYLOAD.json','NKA_RESOLVED_OBJECTS.json','NKA_PHASE1_RESOLVED_OBJECTS.json','NKA_LEDGER17_OBSERVED.json']:
  assert hashlib.sha256(lzma.decompress((E/(n+'.xz')).read_bytes())).hexdigest()==(E/(n+'.sha256')).read_text().strip()
 assert not subprocess.check_output(['git','diff',a['frozen_revision'],'--name-only','--','crates','programs','Cargo.lock'],text=True).strip(),'shipped files differ'
 assert all(p.stat().st_size<=20000000 for p in E.rglob('*') if p.is_file())
 assert not list(E.rglob('__pycache__'))
 forbidden=[]
 for m in modules:
  text=(E/m['source']).read_text()
  if re.search(r'\b(?:sorry|axiom|native_decide)\b|set_option maxHeartbeats|XRn_Join',text):forbidden.append(m['source'])
 assert not forbidden,forbidden
 out=dict(status='PASS',checks='final gate,40raw roots,14current sources,matched controls,offline frozen graph+lock,KMX hash,all original caller clauses,conservative edges,archive hashes,unchanged shipped files,size/hygiene',mutation_cases=mutants,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
 (E/'NKA_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',mutations_rejected=len(mutants),proof_modules=len(modules))))
if __name__=='__main__':main()
