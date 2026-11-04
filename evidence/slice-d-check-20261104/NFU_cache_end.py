"""After final scopes: retain and hash own objects, reclaim only own build scratch."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
code=r'''
from pathlib import Path
import hashlib,json,shutil,subprocess
B=Path('/home/dombarker/project-offloads/codex-cx-slice-d-check-20261104');C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-check-cache-20261104');out=C/'NFU_exports_20261104'
assert all((B/f'NFU_K{i:03}'/'receipt.json').is_file()for i in range(1,101))
assert json.loads((B/'NFU_L060/receipt.json').read_text())['exit_status']==0
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
exports={}
for directory in ['NFU_objects','NFU_generated']:
 for p in sorted((B/directory).rglob('*')):
  if not p.is_file():continue
  rel=p.relative_to(B/directory);q=out/rel;q.parent.mkdir(parents=True,exist_ok=True)
  h=sha(p)
  if q.exists():assert sha(q)==h,str(q)
  else:shutil.copy2(p,q)
  assert sha(q)==h
  exports[str(rel)]=dict(sha256=h,bytes=q.stat().st_size,source=str(p))
assert exports
removed=[]
for name in ['NFU_target','NFU_ref_target','NFU_objects']:
 p=B/name;assert p.parent==B and not p.is_symlink()
 if p.exists():shutil.rmtree(p);removed.append(str(p))
# Solver TMPDIR is job-private. No shared /tmp or cache path is removed.
solver=[]
for pat in ['external-sat*.cnf','smt2_dec_problem*']:
 for p in (B/'NFU_tmp').glob(pat):
  if p.is_file():p.unlink();solver.append(str(p))
units=subprocess.run(['systemctl','--user','list-units','--type=scope','--state=running','--no-pager','--no-legend'],capture_output=True,text=True)
print(json.dumps(dict(exports=str(out),export_objects=exports,retained_cache=str(C),cache_retained=True,cache_deleted=False,removed_own_build_scratch=removed,removed_own_solver_files=solver,restore='Copy retained NFU_exports_20261104 contents into NFU_objects before reusing the pinned receipt LEAN_PATH; verify these hashes. NFU_generated sources stay in workspace.',build_targets_absent={n:not(B/n).exists()for n in ['NFU_target','NFU_ref_target','NFU_objects']},disk_current=shutil.disk_usage(B)._asdict(),running_scopes_snapshot=units.stdout,retained_native_audit_binaries={str(p):dict(sha256=sha(p),bytes=p.stat().st_size)for p in (B/'NFU_native').glob('*')if p.is_file()and p.name in ['NFU_ProofDriver','NFU_Stage2Driver']},source_and_receipts_retained=True,no_shared_path_or_key_cleanup=True)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NFU_CACHE_END_transport.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr,mutation_submitted=True,no_resubmit=True),indent=1)+'\n')
assert r.returncode==0,'Submitted once; recover read-only if transport failed: '+r.stderr
x=json.loads(r.stdout);assert x['export_objects']and all(x['build_targets_absent'].values())
(E/'NFU_CACHE_END.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(exports=x['exports'],objects=len(x['export_objects']),cache_retained=True,free_bytes=x['disk_current']['free'])))
