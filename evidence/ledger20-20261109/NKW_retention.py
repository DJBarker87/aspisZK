from pathlib import Path
import subprocess,json,hashlib,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-ledger20-20261109';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKW_20261109'
seeds=json.loads((E/'NKW_SEED_INPUTS.json').read_text());exports=json.loads((E/'NKW_EXPORT.json').read_text())['files']
code='''from pathlib import Path
import json,hashlib,shutil,subprocess
b=Path(B);c=Path(C);checked=[]
for r in seeds:
 p=c/(r['tag']+'_seed')/r['relative'];assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];checked.append(str(p))
for r in exports:
 p=Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
print(json.dumps(dict(status='PASS',seed_files_rehashed=len(checked),export_files_rehashed=len(exports),disk=shutil.disk_usage(b)._asdict(),own_workspace_bytes=int(subprocess.check_output(['du','-sb',str(b)]).split()[0]),own_cache_bytes=int(subprocess.check_output(['du','-sb',str(c)]).split()[0]),TMPDIR_retained=(b/'NKW_tmp').is_dir(),cache_retained=c.is_dir(),deletions=0)))
'''
for i in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nseeds='+repr(seeds)+'\nexports='+repr(exports)+'\n'+code,text=True,capture_output=True)
 (E/f'NKW_retention-{i}.log').write_text(r.stdout+r.stderr)
 if r.returncode!=255:break
 if i<10:time.sleep(60)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);assert x['disk']['free']>=40_000_000_000 and x['TMPDIR_retained']and x['cache_retained'];(E/'NKW_FINAL_HOST.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
