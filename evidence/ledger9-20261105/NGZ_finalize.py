"""Reconcile exact raw ax2 output, same-binary fixtures and full loaded scan."""
from pathlib import Path
import json,lzma,hashlib,collections,re
E=Path(__file__).resolve().parent;J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest();STD={'propext','Classical.choice','Quot.sound'}
receipts={p.parent.name:J(p)for p in E.glob('NGZ_L*/receipt.json')}
assert len(receipts)==40,len(receipts)
for a,r in receipts.items():
 ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and int(r['swaps'])==0
 assert r['exit_status']==(1 if a in ['NGZ_L001','NGZ_L002','NGZ_L033']else 0),(a,r['exit_status'])
 if r['kind']=='lean':assert '-M7000'in r['command']
 if r['kind']=='link':assert '-O3'in r['command']
expected=J(E/'NGZ_AUDIT_ROOTS.json')['roots'];results=[];binary=None
for i in range(24):
 a='NGZ_L'+str(i+8).zfill(3);x=J(E/'NGZ_audit'/('batch'+str(i))/('proof'+str(i)+'.json'));assert x['exit_status']==0
 bp=J(E/a/'NGZ_ProofDriver_BINARY_PIN.json');binary=binary or bp;assert binary==bp
 for r in x['results']:
  assert set(r['walked_axioms'])<=STD and set(r['collect_axioms'])<=STD and r['equal'],r['root']
  name='NGZ_NEP_proof'+str(i)+'_'+r['root']+'_REACHABLE.txt';p=E/(name+'.xz');raw=lzma.decompress(p.read_bytes());assert H(raw)==(E/(name+'.sha256')).read_text().strip()
  results.append(dict(r,attempt=a,raw_graph=p.name,raw_graph_sha256=H(raw),archive_sha256=H(p.read_bytes())))
assert len(results)==len(expected)==len({r['root']for r in results})and {r['root']for r in results}==set(expected)
fx=J(E/'NGZ_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and len(fx['results'])==8 and all(r['equal']for r in fx['results']);assert all(r['walked_axioms']for r in fx['results'][:4])and all(not r['walked_axioms']for r in fx['results'][4:]);assert J(E/'NGZ_L032/NGZ_ProofDriver_BINARY_PIN.json')==binary
walker=J(E/'NGZ_WALKER_CONFORMANCE.json');assert walker['byte_identical']and H((E/'NGZ_WALKER_SOURCE.lean.txt').read_bytes())==walker['sha256']
historical=J(E.parent/'pool-retarget-20261105/NGK_L051/receipt.json')
oldwalker=next(v['sha256']for p,v in historical['deps_fingerprint']['selected_objects'].items()if p.endswith('/NFA_WALKER.olean'))
walker_objects={}
for a,r in receipts.items():
 if r['kind']=='audit':
  p,v=next((p,v)for p,v in r['deps_fingerprint']['selected_objects'].items()if p.endswith('/NFA_WALKER.olean'))
  assert v['sha256']==oldwalker
  walker_objects[p]=v
walker['compiled_object_pins']=walker_objects
walker['historical_conformance']='NGK_L051 same NFA_WALKER object; byte-identical canonical source rechecked here'
assert J(E/'NGZ_L033/NGZ_Driver_BINARY_PIN.json')==J(E/'NGZ_L034/NGZ_Driver_BINARY_PIN.json')
rows=[json.loads(l)for l in (E/'NGZ_LOADED_scan.jsonl').read_text().splitlines()];bad=[r for r in rows if r['dangling']or r['duplicate_owners']or not r['imports_match']]
scan=dict(status='PASS'if not bad else'FAIL',modules=len(rows),declarations=sum(r['declarations']for r in rows),edges=sum(r['edges']for r in rows),dangling=sum(len(r['dangling'])for r in rows),incompatible_owners=sum(len(r['duplicate_owners'])for r in rows),import_mismatches=sum(not r['imports_match']for r in rows),compatible_cached_replicas=sum(len(r['cached_replicas'])for r in rows),defects=bad,scan_sha256=H((E/'NGZ_LOADED_scan.jsonl').read_bytes()))
required=set(re.findall(r'^import ([\w.]+)',(E/'NGZ_COMBINED_IMPORT.lean').read_text(),re.M));assert required<={r['module']for r in rows};scan['required_forests_loaded']=sorted(required)
(E/'NGZ_SCAN.json').write_text(json.dumps(scan,indent=1)+'\n')
conflicts=dict(status='NONE'if not bad else'FINDING',conflicts=[r for r in bad if r['duplicate_owners']],qualified_rows=[],reason='No row is qualified when full composed closure scans clean; canonical NGK forest replaces legacy conflict',full_import_attempt='NGZ_L003',scan_attempt='NGZ_L034')
(E/'NGZ_CONFLICTS.json').write_text(json.dumps(conflicts,indent=1)+'\n')
audit=dict(status='PASS'if not bad else'FAIL_SCAN',root_count=len(results),results=results,fixtures=fx['results'],same_proof_binary=binary,collect_axioms_disagreements=[r['root']for r in results if not r['equal']],walker_conformance=walker,headline='AspisR1.RPx_Deployed.deployed',combined_import='NGZ_L003',scan='NGZ_SCAN.json',no_new_theorem=True,cold_release_replay=False)
(E/'NGZ_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
metrics=dict(charged_slots=len(receipts),by_kind=dict(collections.Counter(r['kind']for r in receipts.values())),successful=sum(r['exit_status']==0 for r in receipts.values()),failures={a:r['exit_status']for a,r in receipts.items()if r['exit_status']},scope_wall_sum_seconds=sum(r['wall_seconds']for r in receipts.values()),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts.values()),swaps=0,Kani=0,extraction=0,new_theorems=0,caps='MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; Lean -M7000',timeouts=0,memory_kills=0)
(E/'NGZ_METRICS.json').write_text(json.dumps(metrics,indent=1)+'\n')
print(json.dumps(dict(roots=len(results),scan=scan,metrics=metrics)));assert not bad,'Scanner findings retained; never claim clean'
