"""Remove only this job's rebuildable host caches; preserve sources/receipts."""
from pathlib import Path
import hashlib,json,os,shutil,time
B=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-2-20261027')
live=[]
for p in Path('/proc').glob('[0-9]*/cmdline'):
 try:
  cmd=p.read_bytes().decode(errors='replace');exe=Path(os.readlink(p.parent/'exe')).name
  if str(B) in cmd and exe in ['lean','cbmc','cargo-kani','kani-driver','kani-compiler','rustc','cargo']:live.append({'pid':p.parent.name,'exe':exe,'command':cmd.replace('\x00',' ')})
 except (OSError,ProcessLookupError):pass
assert not live,live
objects={str(p):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in (B/'LPb_objects').glob('*') if p.is_file()}
receipt=json.loads((B/'LPb_L037/receipt.json').read_text())
checked={k:{**v,'matches':Path(v['path']).is_file() and hashlib.sha256(Path(v['path']).read_bytes()).hexdigest()==v['sha256']} for k,v in receipt['deps_fingerprint']['selected_objects'].items()}
assert all(v['matches'] for v in checked.values())
start=json.loads((B/'LPb_K001-reservation.json').read_text())['utc']
residuals=[]
for pattern in ['external-sat*.cnf','smt2_dec_problem*']:
 for p in Path('/tmp').glob(pattern):
  if p.is_file():residuals.append({'path':str(p),'mtime':p.stat().st_mtime,'bytes':p.stat().st_size,'predates_job':p.stat().st_mtime<start,'action':'retained; not proven owned by LPb'})
removed={}
for n in ['LPb_target','LPb_objects','LPb_crate','.lake']:
 p=B/n
 if p.is_dir():
  removed[n]=sum(x.stat().st_size for x in p.rglob('*') if x.is_file() and not x.is_symlink());shutil.rmtree(p)
result={'utc':time.time(),'own_live_build_processes':live,'objects_before_cleanup':objects,'final_selected_objects_checked_before_cleanup':checked,'removed_rebuildable_directories_bytes':removed,'removed_bytes':sum(removed.values()),'tmp_solver_candidates':residuals,'shared_coherent_and_XRn_caches':'retained untouched','own_sources_receipts_active_lock':'retained in evidence; Cargo lock also archived locally','keys':'none created or touched'}
(B/'LPb_cleanup.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'removed_bytes':result['removed_bytes'],'own_live_build_processes':live,'tmp_solver_candidates':len(residuals),'all_tmp_candidates_predate_job':all(r['predates_job'] for r in residuals)}))
