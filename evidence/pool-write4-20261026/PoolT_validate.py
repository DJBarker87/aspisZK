"""Read-only proof/source/receipt validation, not build or monitoring infrastructure."""
from pathlib import Path
import hashlib,json,re,subprocess
B=Path(__file__).resolve().parent;R=B.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(B.glob('PoolT_*/receipt.json'))]
lean=[r for r in receipts if r['kind']=='lean'];kani=[r for r in receipts if r['kind']=='kani']
assert len(lean)==59 and len(kani)==15
caps={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==caps and r['swaps']=='0'
 for name,h in r['source_hashes'].items():assert sha(B/r['attempt']/'sources'/name)==h,(r['attempt'],name)
 if r['kind']=='lean':
  assert '-M7000' in r['command']
  if r['exit_status']==0:
   for a in r['print_axioms']:
    assert 'sorryAx' not in a
    if '[' in a:assert {x.strip() for x in a.split('[')[1].split(']')[0].split(',')}<={'propext','Classical.choice','Quot.sound'}
 else:
  assert r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3' and r['env']['CARGO_BUILD_JOBS']=='4'
  assert '--harness' in r['command']
modules=[]
for p in sorted((R/'lean').glob('PoolT_*.lean')):
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option (maxHeartbeats|maxRecDepth)',p.read_text())
 passed=[r for r in lean if r['exit_status']==0 and r['source_hashes'].get(p.name)==sha(p)]
 assert passed,p
 modules.append({'module':p.name,'sha256':sha(p),'receipt':passed[-1]['attempt']+'/receipt.json'})
freeze=json.loads((B/'PoolT_FREEZE.json').read_text())
for name,pin in freeze['source_pins'].items():assert sha(R/name)==pin['sha256'],name
inputs=json.loads((B/'PoolT_INPUTS.json').read_text())['inputs']
for row in inputs:assert sha(R/row['path'])==row['sha256'],row['path']
host=json.loads((B/'PoolT_HOST_INPUT_MATCH.json').read_text());assert host['inputs']==len(inputs) and not host['mismatches']
source=json.loads((B/'PoolT_SOURCE.json').read_text());native=R/source['original']['path'];assert sha(native)==source['original']['sha256']
for text in source['slices'].values():assert text in native.read_text()
snapshot=json.loads((B/'PoolT_SNAPSHOT_SOURCE.json').read_text());assert sha(R/snapshot['path'])==snapshot['sha256'];assert snapshot['exact_body'] in (R/snapshot['path']).read_text();assert snapshot['exact_body'] in (B/'PoolT_snapshot/PoolT_lib.rs').read_text()
changed=subprocess.check_output(['git','diff','--name-only','546891795f5060bd2f71784bb9fee05b34bba001'],cwd=R,text=True).splitlines()
assert all(p.startswith('lean/PoolT_') or p.startswith('evidence/pool-write4-20261026/PoolT_') for p in changed),changed
assert not any(p.suffix in {'.olean','.so','.bin','.llbc','.gz','.tar','.elf'} for p in B.rglob('*') if p.is_file())
audit=next(r for r in lean if r['attempt']=='PoolT_L060');assert audit['exit_status']==0 and len(audit['print_axioms'])==10
summary={'status':'pass','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'dirty_source_snapshots_recorded':True,'lean_actual_compiles':len(lean),'lean_submissions':60,'lean_preflight_rejection':{'attempt':'PoolT_L055','reason':'PoolT_Snapshot prerequisite not yet green; no Lean launched'},'lean_passed':sum(r['exit_status']==0 for r in lean),'kani_runs':len(kani),'kani_passed':sum(r['exit_status']==0 for r in kani),'lean_allowance_exhausted':False,'kani_missing_leaf_allowance_exhausted':True,'current_modules':modules,'caps':caps,'all_swap_zero':True,'inherited_compiler_inputs_checked_locally_and_host':len(inputs),'native_p1_certificate_established':False,'verifier_local_copy_certificate_established':True,'global_s2_rows_removed':0,'new_runtime_item':False,'shipped_changes':False,'elf_rebuild_trigger':False,'inherited_elf_pins':freeze['elf_pins'],'measurement_caveat':'K011/K012 time-reported peakRSS2112 KiB is incomplete descendant measurement; raw cgroup_memory_peak_bytes retained separately; no aggregate-RSS claim','audit':{k:audit[k] for k in ['attempt','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']}}
(B/'PoolT_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(B/'PoolT_ATTEMPTS.json').write_text(json.dumps([{'receipt':r['attempt']+'/receipt.json',**{k:r[k] for k in ['attempt','kind','command','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','source_revision','source_hashes','deps_fingerprint','print_axioms']}} for r in receipts],indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['status','lean_actual_compiles','lean_passed','kani_runs','kani_passed','native_p1_certificate_established','verifier_local_copy_certificate_established']}))
