"""Final ax2 evidence: list-only driver plus independently strengthened scan."""
from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=(E.parent/'slice-q-mul7-20261104/NFF_Driver.lean').read_text();proof=(E/'NFN_ProofDriver.lean').read_text()
prefix=lambda s:s[:s.index('/-- Standalone runtime')]
action=lambda s:s[s.index('  let ctx : Command.Context'):]
assert prefix(base)==prefix(proof) and action(base)==action(proof)
assert 'importAll := true' in proof and '(level := .private)' in proof
assert obj(E/'NFN_WALKER_IDENTITY.json')['byte_identical']
parent=obj(E/'NFN_L070/receipt.json');compiled=obj(E/'NFN_L069/receipt.json')
assert parent['exit_status']==compiled['exit_status']==0
assert compiled['source_hashes']['NFN_generated/NFN_ProofDriver.lean']==sha(E/'NFN_ProofDriver.lean')
assert parent['source_hashes']['NFN_generated/NFN_ProofDriver.lean']==sha(E/'NFN_ProofDriver.lean')
summary=obj(E/'NFN_final_audit/SUMMARY.json');assert summary['status']=='PASS'
controls=obj(E/'NFN_final_audit/fixtures.json')['results'];assert len(controls)==8 and all(x['equal'] for x in controls)
assert all(len(x['walked_axioms'])==1 for x in controls[:4]) and all(not x['walked_axioms'] for x in controls[4:])
primary=[];query=[]
for command in summary['commands']:
 assert command['exit_status']==0 and command['swaps']=='0'
 if command['target'] in ['link','fixtures']:continue
 for r in command['results']:
  assert r['equal'] and set(r['collect_axioms'])==set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
  name='NEP_'+command['target']+'_'+r['root']+'_REACHABLE.txt';p=E/(name+'.xz');plain=lzma.decompress(p.read_bytes());h=hashlib.sha256(plain).hexdigest()
  assert (E/(name+'.sha256')).read_text().split()[0]==h
  row={**r,'attempt':'NFN_L070','batch_target':command['target'],'graph_archive':p.name,'archive_sha256':sha(p),'uncompressed_sha256':h}
  (query if command['target'].startswith('query') else primary).append(row)
assert {r['root'] for r in primary}==set(obj(E/'NFN_AUDIT_ROOTS.json'))
assert len(query)==5 and all(x['root'].startswith('NFN_QueryModel.') for x in query)
old=obj(E/'NFN_PRELIMINARY_AUDIT.json')
scan=obj(E/'NFN_L066/receipt.json');loaded=list(map(json.loads,(E/'NFN_QUERY_LOADED_scan.jsonl').read_text().splitlines()))
assert scan['exit_status']==0 and all(x['imports_match'] and not x['dangling'] and not x['duplicate_owners'] for x in loaded)
conformance=dict(status='PASS',baseline='evidence/slice-q-mul7-20261104/NFF_Driver.lean',unchanged_pre_runtime_prefix=True,unchanged_raw_audit_action=True,driver_file='NFN_ProofDriver.lean',driver_sha256=sha(E/'NFN_ProofDriver.lean'),diff='NFN_PROOF_DRIVER.diff',diff_sha256=sha(E/'NFN_PROOF_DRIVER.diff'),walker=obj(E/'NFN_WALKER_IDENTITY.json'),fixture_attempt='NFN_L070/fixtures',fixtures=controls,binary=obj(E/'NFN_final_audit/BINARY_PIN.json'),scan_separate=True)
(E/'NFN_AX2_CONFORMANCE.json').write_text(json.dumps(conformance,indent=1)+'\n')
old.update(driver_file='NFN_ProofDriver.lean',driver_source_sha256=sha(E/'NFN_ProofDriver.lean'),driver_diff='NFN_PROOF_DRIVER.diff',driver_diff_sha256=sha(E/'NFN_PROOF_DRIVER.diff'),driver_binary=conformance['binary'],fixture_attempt='NFN_L070/fixtures',fixtures=controls,results=primary,roots=20,scopes=summary['commands'],ax2_conformance_sha256=sha(E/'NFN_AX2_CONFORMANCE.json'),audit_batch={k:parent[k] for k in ['attempt','kind','command','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','limits']},preliminary='NFN_PRELIMINARY_AUDIT.json; superseded as the final ax2 driver admission, retained for diagnostics')
(E/'NFN_AUDIT.json').write_text(json.dumps(old,indent=1)+'\n')
q=dict(status='PASS_MODEL_ONLY_NO_ROOT_PROMOTION',module='NFN_QueryModel',module_source_sha256=sha(E/'NFN_QueryModel.lean'),compile=obj(E/'NFN_L065/receipt.json'),results=query,fixtures=controls,driver=conformance,scan=dict(attempt='NFN_L066',modules=len(loaded),declarations=sum(x['declarations'] for x in loaded),references=sum(x['edges'] for x in loaded),dangling=0,duplicate_owners=0,import_mismatches=0,sha256=sha(E/'NFN_QUERY_LOADED_scan.jsonl'),**{k:scan[k] for k in ['source_revision','exit_status','wall_seconds','peak_rss_kib','swaps']}),native_association='OPEN: original query_values caller/domain/Option<fn> association; no NFN native packet',newly_closed=[])
(E/'NFN_QUERY_AUDIT.json').write_text(json.dumps(q,indent=1)+'\n')
print(json.dumps(dict(ax2='PASS',primary_roots=len(primary),model_roots=len(query),fixtures=len(controls),final_audit_batch_seconds=parent['wall_seconds'])))
