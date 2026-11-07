from PCD_transport import *
import hashlib
admission('PCD_SEED')
r=ssh('python3',f'''from pathlib import Path
import json,shutil,hashlib
b=Path({B!r});records=[]
base=Path('/home/dombarker/project-offloads/codex-cx-ledger23-20261110/NLS_L001.json')
env=json.loads(base.read_text())['env']
selections=[('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NLS_20261110/NLS_exports_20261110','NLS_','NLS_seed'),('/home/dombarker/project-offloads/codex-cx-sdk-borrow-20261109/NLF_exports_20261109_72e6c5ce1014','NLF_','NLF_seed')]
for root,prefix,target in selections:
 for p in Path(root).rglob('*'):
  if not p.is_file() or not p.name.startswith(prefix):continue
  q=b/target/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copy2(p,q)
  records.append(dict(source=str(p),target=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
s=Path('/home/dombarker/project-offloads/codex-cx-sdk-borrow-20261109')
for n in ['S2W_lean_host.py','S2W_run_host.py','lean-toolchain','lakefile.toml','lake-manifest.json']:
 q=b/n
 if q.exists():assert q.read_bytes()==(s/n).read_bytes()
 else:shutil.copy2(s/n,q)
 records.append(dict(source=str(s/n),target=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for n in ['PCD_objects','PCD_tmp','PCD_generated','PCD_native']:(b/n).mkdir(exist_ok=True)
# Original coherent roots are read-only fallbacks; private copies take priority.
env['LEAN_PATH']=':'.join([str(b/'NLS_seed'),str(b/'NLF_seed')]+env['LEAN_PATH'].split(':'))
print(json.dumps(dict(env=env,files=records,base=str(base),base_sha256=hashlib.sha256(base.read_bytes()).hexdigest(),free_bytes=shutil.disk_usage(b).free)))
''')
assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
(E/'PCD_SEED.json').write_text(json.dumps({k:v for k,v in out.items() if k!='env'},indent=1)+'\n')
(E/'PCD_ENV_BASE.json').write_text(json.dumps({'env':out['env']},indent=1)+'\n')
print('PCD private seed copied and hashes recorded; coherent inherited roots remain read-only.')
