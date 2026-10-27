from pathlib import Path
import hashlib,json
B=Path(__file__).resolve().parent
O=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027')
def sha(p):return hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
old=json.loads((O/'XRa_HostArtifacts.json').read_text());rows=[]
for r in old['retained_artifacts']:
 p=Path(r['path']);h=sha(p);rows.append({**r,'actual_sha256':h,'match':h==r['sha256'] and p.stat().st_size==r['bytes']})
pins=json.loads((O/'XRa_release_sourcepins.json').read_text());root=Path('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/src')
errors=[r['path'] for r in pins['files'] if sha(root/r['path'])!=r['sha256']]
artifacts=[]
for p in sorted(B.glob('XRb_*')):
 if p.is_file() and p.suffix=='.llbc':
  artifacts.append({'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size,'removed':True,'reason':'task-owned diagnostic derivative, reproducible from retained script; original pinned LLBC retained read-only'})
  p.unlink()
runner=B/'S2W_run_host.py'
out={'retained_artifact_checks':rows,'release_revision':pins['source_revision'],'release_source_files_checked':len(pins['files']),'release_source_errors':errors,'runner_sha256':sha(runner),'inherited_runner_sha256':sha(O/'S2W_run_host.py'),'runner_unchanged':sha(runner)==sha(O/'S2W_run_host.py'),'removed_diagnostic_derivatives':artifacts,'Charon_Aeneas_invocations_in_this_audit':0,'axioms':'N/A: no Lean theorem','no_compiled_object_or_cargo_cache_created':True}
(B/'XRb_HostAudit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['retained_artifact_checks','removed_diagnostic_derivatives']},indent=2))
assert all(r['match'] for r in rows) and not errors and out['runner_unchanged']
