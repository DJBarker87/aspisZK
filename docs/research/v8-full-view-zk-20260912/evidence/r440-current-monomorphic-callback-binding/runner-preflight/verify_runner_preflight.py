#!/usr/bin/env python3
"""Read-only integrity/static gate for the prepared R440 runner adaptation."""
import ast,hashlib,json,sys
from pathlib import Path
ROOT=Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
B=ROOT/'.r21-scratch/r440-mono-closure-binding/runner-preflight'
errors=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((B/'template-manifest.json').read_text())
for e in manifest['files']:
 src=ROOT/e['source_path'];dst=B/e['template_path']
 if not src.is_file() or src.read_bytes()!=dst.read_bytes() or sha(dst)!=e['sha256']:errors.append('prior template mismatch: '+e['template_path'])
for version,source_dir,names in [
 ('v1',ROOT/'.r21-scratch/r440-mono-closure-binding/candidate-b',['candidate-b.json','candidate-b.patch','main.original.rs','main.candidate.rs','translate_closures.candidate.rs']),
 ('v2',ROOT/'.r21-scratch/r440-mono-closure-binding/candidate-b-v2',['candidate-b-v2.json','candidate-b-v2.patch','main.original.rs','main.candidate.rs','translate_closures.original.rs','translate_closures.candidate.rs'])]:
 for n in names:
  src=source_dir/n;dst=(B/'candidate-b-artifacts'/n) if version=='v1' else (B/'candidate-b-v2-artifacts'/n)
  if not src.is_file() or not dst.is_file() or src.read_bytes()!=dst.read_bytes():errors.append(f'{version} candidate copy mismatch: {n}')
meta=json.loads((ROOT/'.r21-scratch/r440-mono-closure-binding/candidate-b-v2/candidate-b-v2.json').read_text())
pins=json.loads((B/'candidate-b-pins-v2.unreviewed.json').read_text())
if meta['status']!='UNBUILT_LOCAL_DIAGNOSTIC_CANDIDATE_B_V2':errors.append('unexpected candidate v2 status')
if pins['status']!='candidate-b-v2-pins-pending-lead-review':errors.append('candidate v2 review gate is not pending')
if pins['candidate_json_sha256']!=sha(ROOT/'.r21-scratch/r440-mono-closure-binding/candidate-b-v2/candidate-b-v2.json'):errors.append('candidate v2 metadata hash mismatch')
if pins['patch_sha256']!=sha(ROOT/'.r21-scratch/r440-mono-closure-binding/candidate-b-v2/candidate-b-v2.patch'):errors.append('candidate v2 patch hash mismatch')
for row in pins['overlays']:
 key='main' if row['path'].endswith('/main.rs') else 'closure'
 expected=meta['candidate_main_sha256'] if key=='main' else meta['candidate_closure_sha256']
 if row['candidate_sha256']!=expected:errors.append('v2 candidate overlay pin mismatch: '+key)
worker=B/'run_direct_driver_r440_unverified.py';clone=B/'prepare_clone_r440_unverified.py'
for p in [worker,clone]:ast.parse(p.read_text(),filename=str(p))
w=worker.read_text();c=clone.read_text()
for needle in ['5*1024**3','7*1024**3',"'0'", "'128'",'opt-level=3','codegen-units=16','reviewed-candidate-b-pins','tracked_candidate_sha256_after_overlay','candidate_wrapper_source_sha256']:
 if needle not in w:errors.append('worker missing invariant: '+needle)
for needle in ["'memory.high'","'memory.max'","'memory.swap.max'","'pids.max'",'git','git_blob_sha1','only_tracked_source_differences','target_cache_copied','--system','assert finite']:
 if needle not in c:errors.append('clone preparer missing invariant: '+needle)
for needle in ["'memory.high'","'memory.max'","'memory.swap.max'","'pids.max'",'--system','assert finite','aspis-r440-direct-driver.service']:
 if needle not in w:errors.append('worker missing resource invariant: '+needle)
if 'shutil.copytree(cache_src' in c or "'charon/target'" in c and 'copytree' in c:errors.append('clone preparer appears to copy target cache')
if "assert pins.get('status')=='reviewed-candidate-b-pins'" not in c:errors.append('clone preparer missing lead-review gate')
if "assert bpins.get('status')=='reviewed-candidate-b-pins'" not in w:errors.append('build worker missing lead-review gate')
plan=json.loads((B/'launch-plan-r440.pending.json').read_text())
if plan['status']!='PREPARED_ONLY_NOT_LAUNCHED' or not plan['no_build_or_remote_mutation_performed']:errors.append('plan does not remain unlaunched')
if plan['systemd_unit']!='aspis-r440-direct-driver.service':errors.append('plan unit does not match worker own-unit exclusion')
if plan['clone_systemd_unit']!='aspis-r440-source-clone.service':errors.append('plan clone unit does not match preparer own-unit exclusion')
report={'status':'PASS' if not errors else 'FAIL','previous_runner_templates_byte_verified':len(manifest['files']),'candidate_b_v2_status':meta['status'],'candidate_b_v2_json_sha256':sha(ROOT/'.r21-scratch/r440-mono-closure-binding/candidate-b-v2/candidate-b-v2.json'),'candidate_b_v2_patch_sha256':sha(ROOT/'.r21-scratch/r440-mono-closure-binding/candidate-b-v2/candidate-b-v2.patch'),'source_only_clone_preparer_sha256':sha(clone),'direct_driver_worker_sha256':sha(worker),'both_python_ast_parses':'PASS','review_status_gate_fails_closed':pins['status']!='reviewed-candidate-b-pins','source_cache_clone':'none; worker reads pinned original cache only','remote_mutation_or_build_performed':False,'errors':errors}
(B/'runner-preflight-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2));sys.exit(bool(errors))
