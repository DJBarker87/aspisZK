#!/usr/bin/env python3
"""Read-only source/receipt/axiom/scope validation; no proof/build launcher."""
from pathlib import Path
import hashlib,json,re,subprocess,time,resource
start=time.monotonic();root=Path(__file__).resolve().parents[2];p=Path(__file__).resolve().parent
receipts=[json.loads(f.read_text()) for f in sorted(p.glob('SAP_*/receipt.json'))]
assert len(receipts)==100
assert all(r['swaps']=='0' for r in receipts)
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert all(r['limits']==limits for r in receipts)
assert all('-M7000' in r['command'] for r in receipts)
final=next(r for r in receipts if r['attempt']=='SAP_101');assert final['exit_status']==0
assert len(final['print_axioms'])==82
allowed={'propext','Classical.choice','Quot.sound'}
for line in final['print_axioms']:
 for match in re.findall(r'depends on axioms: \[([^\]]*)\]',line):
  assert {s.strip() for s in match.split(',')}<=allowed,line
accepted={}
for r in receipts:
 if r['exit_status']==0:
  for name,sha in r['source_hashes'].items():accepted.setdefault(name,[]).append((sha,r['attempt']))
objects=json.loads((p/'SAP_host_objects.json').read_text());sources={}
for src in sorted((root/'lean').glob('SAP_*.lean')):
 sha=hashlib.sha256(src.read_bytes()).hexdigest();matches=[a for h,a in accepted.get(src.name,[]) if h==sha]
 assert matches,src
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',src.read_text()),src
 obj=objects[src.with_suffix('.olean').name];assert obj['source_sha256']==sha,src
 sources[str(src.relative_to(root))]={'sha256':sha,'passing_attempts':matches,'object_sha256':obj['sha256']}
base='b6bc3d3965f5f40c48c64835747b5c1b8cbddb19'
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=root,text=True).splitlines()
assert all(x.startswith(('lean/SAP_','evidence/sessa-prepare-20261026/')) for x in changed)
subprocess.run(['git','diff','--check'],cwd=root,check=True)
nonvac=json.loads((p/'SAP_NONVACUITY.json').read_text());assert not nonvac['mismatches']
inputs=json.loads((p/'SAP_INPUTS.json').read_text())
assert all(hashlib.sha256((root/name).read_bytes()).hexdigest()==sha for name,sha in inputs['files'].items())
report={'lean_used':100,'lean_budget':100,'kani_used':0,'kani_budget':20,'passes':sum(r['exit_status']==0 for r in receipts),
 'failed_attempts':[r['attempt'] for r in receipts if r['exit_status']],
 'preflight_only':['SAP_005'],'reservation_retries':['SAP_087: vanished non-own cgroup,wait30 seconds,one successful retry'],
 'final_audit':{k:final[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes']},
 'axiom_reports':len(final['print_axioms']),'accepted_axioms':sorted(allowed),'current_sources':sources,
 'peak_rss_all_kib':max(int(r['peak_rss_kib']) for r in receipts),'all_swaps_zero':True,'all_caps_verified':True,
 'no_shipped_changes':True,'ELF_rebuild_triggered':False,'full_manifest_replayed':False,'new_trust_items':[],
 'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
 'wall_seconds':time.monotonic()-start,'peak_rss_self_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(p/'SAP_FINAL.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='current_sources'}))
