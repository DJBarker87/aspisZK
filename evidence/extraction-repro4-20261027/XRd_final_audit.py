from pathlib import Path
import hashlib,json,shutil
B=Path(__file__).resolve().parent
O=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027')
def sha(p):return hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
old=json.loads((O/'XRa_HostArtifacts.json').read_text());rows=[]
for r in old['retained_artifacts']:
 p=Path(r['path']);h=sha(p);rows.append({**r,'actual_sha256':h,'match':h==r['sha256'] and p.stat().st_size==r['bytes']})
pins=json.loads((O/'XRa_release_sourcepins.json').read_text());root=Path('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/src')
errors=[r['path'] for r in pins['files'] if sha(root/r['path'])!=r['sha256']]
artifacts=[]
for name,expected in [('XRd_release_candidate_tx1.llbc','80465ea37dd7c3c5becdd9c413d745ae076adf5b193067e8618d58db075c43e5'),('XRd_without_checkpoint_tx1.llbc','370b8a0a817d7b2b560498fb883b32e885f5522e6b0a4af8304b02219ed64760')]:
 p=B/name;artifacts.append({'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size,'expected':expected,'match':sha(p)==expected,'retained':True,'role':'second pinned release artifact' if 'release_candidate' in name else 'incomplete independent subkit'})
log=B/'XRd_006/stdout.log';lines=log.read_bytes().splitlines(keepends=True)
# Retain the complete log on host; commit a bounded final-context/error excerpt.
excerpt=b''.join(lines[-2000:]);(B/'XRd_006_final_context.log').write_bytes(excerpt)
log_pin={'path':str(log),'sha256':sha(log),'bytes':log.stat().st_size,'retained_on_host':True,'committed_excerpt':'XRd_006_final_context.log','excerpt_sha256':sha(B/'XRd_006_final_context.log'),'excerpt_bytes':len(excerpt),'excerpt_lines':2000,'note':'includes final collapse contexts and complete Not_found stack; full 61MiB log not copied into worktree'}
removed=[]
p=B/'XRd_release_target'
if p.exists():
 removed.append({'path':str(p),'role':'task-owned reproducible Cargo build cache'});shutil.rmtree(p)
runner=B/'S2W_run_host.py'
out={'retained_artifact_checks':rows,'new_artifacts':artifacts,'release_revision':pins['source_revision'],'release_source_files_checked':len(pins['files']),'release_source_errors':errors,'runner_sha256':sha(runner),'inherited_runner_sha256':sha(O/'S2W_run_host.py'),'runner_unchanged':sha(runner)==sha(O/'S2W_run_host.py'),'diagnostic_log':log_pin,'removed_task_caches':removed,'extraction_invocations_in_this_audit':0,'axioms':'N/A: no Lean theorem'}
(B/'XRd_HostAudit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['retained_artifact_checks','new_artifacts','diagnostic_log']},indent=2))
assert all(r['match'] for r in rows+artifacts) and not errors and out['runner_unchanged']
