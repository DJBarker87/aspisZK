from KNB_host import *
code='''from pathlib import Path
import json,hashlib,shutil,subprocess
b=Path('/home/dombarker/project-offloads/codex-cx-kani-diag2-20261028')
out={'removed':[], 'retained_cache':'/home/dombarker/project-offloads/codex-cx-kdiag2-cache-20261028'}
for rel in ['KNB_target','KNB_target_native','KNB_src/target','KNB_tmp']:
 p=b/rel
 if p.exists():
  assert not p.is_symlink(),str(p)
  out['removed'].append(str(p));shutil.rmtree(p)
assert Path(out['retained_cache']).is_dir()
out['kani_binaries']={}
for p in Path('/home/dombarker/.kani').glob('kani-0.67.0*/bin/*'):
 if p.is_file() and p.name in ['kani','cbmc','cadical','goto-instrument','kani-compiler']:
  out['kani_binaries'][str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
  if p.name=='cbmc':out['cbmc_version']=subprocess.run([str(p),'--version'],text=True,capture_output=True).stdout.strip()
print(json.dumps(out,indent=2))
'''
r=py(code);assert r.returncode==0,r.stderr
(E/'KNB_CLEANUP.json').write_text(r.stdout)
