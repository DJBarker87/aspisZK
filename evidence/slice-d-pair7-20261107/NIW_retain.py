"""Read-only retained closure/object/tool inventory; remove only own solver temporaries."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-d-pair7-20261107'
code=r'''from pathlib import Path
import json,hashlib,shutil
b=Path(B)
x=json.loads((b/'NIW_L160.json').read_text());roots=x['env']['LEAN_PATH'].split(':')
def digest(p):
 h=hashlib.sha256()
 with p.open('rb')as f:
  while chunk:=f.read(1048576):h.update(chunk)
 return h.hexdigest()
scan=[json.loads(l)for l in(b/'NIW_final_audit/NIW_LOADED_scan.jsonl').read_text().splitlines()]
files={};missing=[]
for r in scan:
 rel=r['module'].replace('.','/')+'.olean'
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
 if p is None:missing.append(r['module']);continue
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():files[str(z)]={'sha256':digest(z),'bytes':z.stat().st_size}
assert not missing,missing
objects={str(p):{'sha256':digest(p),'bytes':p.stat().st_size}for p in(b/'NIW_objects').glob('NIW_*.olean')}
tools={str(p):{'sha256':digest(p),'bytes':p.stat().st_size}for p in [b/'S2W_run_host.py',b/'S2W_lean_host.py',Path(x['env']['LEAN_SYSROOT'])/'bin/lean',Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-driver')]if p.is_file()}
removed=[]
for p in (b/'NIW_tmp').rglob('*'):
 if p.is_file() and (p.name.startswith('external-sat')and p.suffix=='.cnf' or p.name.startswith('smt2_dec_problem')):
  removed.append({'path':str(p),'bytes':p.stat().st_size});p.unlink()
result={'workspace':str(b),'cargo_target_dir':x['env']['CARGO_TARGET_DIR'],'lean_path':roots,'source':'actual loaded-module list in final NIW_L160 scan, first matching recorded LEAN_PATH path','modules':len(scan),'closure_files':files,'own_objects':objects,'tools':tools,'removed_own_solver_temporary_files':removed,'disk_free_bytes':shutil.disk_usage(b).free,'retained':['NIW_seed','NIW_objects','NIW_target','NIW_native','all host attempt directories'],'no_workspace_or_cache_deleted':True}
(b/'NIW_RETENTION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
'''
code='B='+repr(B)+'\n'+code
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
 with(E/'NIW_RETENTION_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps({'retry':retry,'exit':r.returncode,'stderr':r.stderr})+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
j=json.loads(r.stdout);(E/'NIW_RETENTION.json').write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps({k:j[k]for k in ['modules','disk_free_bytes','no_workspace_or_cache_deleted']}))
