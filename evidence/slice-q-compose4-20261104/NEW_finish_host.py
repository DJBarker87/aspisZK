"""Export checked own Lean objects and remove only rebuildable own scratch."""
from NEW_remote import *
assert not (E/'NEW_ACTIVE.json').exists()
a='NEW_FINAL_CACHE';admit(a)
proofs=json.loads((E/'NEW_PROOF_AUDIT.json').read_text())['accepted']
code=f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});c=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose4-cache-20261029');out=c/'NEW_exports_20261104'
proofs={proofs!r};exports=[];removed=[]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while x:=f.read(1048576):h.update(x)
 return h.hexdigest()
for item in proofs:
 mod=Path(item['module'].replace('.','/'));src=b/mod.with_suffix('.lean')
 assert src.is_file() and sha(src)==item['sha256'],str(src)
 found=False
 for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
  p=b/(str(mod)+suffix)
  if not p.is_file():continue
  found=found or suffix=='.olean';dest=out/p.relative_to(b);dest.parent.mkdir(parents=True,exist_ok=True)
  h=sha(p)
  if dest.exists():assert sha(dest)==h,str(dest)
  else:shutil.copy2(p,dest)
  assert sha(dest)==h
  exports.append(dict(module=item['module'],attempt=item['attempt'],source=str(p),destination=str(dest),sha256=h,bytes=p.stat().st_size))
 assert found,item['module']
# Explicit own build output directories only. Sources, receipts and every cache survive.
for p in b.rglob('target'):
 if not p.is_dir() or p.is_symlink():continue
 if not p.resolve().is_relative_to(b.resolve()):raise RuntimeError(str(p))
 removed.append(dict(path=str(p),kind='cargo-target'));shutil.rmtree(p)
for name in ['NEW_target','NEW_fidelity_target','NEW_extract_target','NEW_geometry_extract_target']:
 p=b/name
 if p.is_dir():removed.append(dict(path=str(p),kind='own-build-output'));shutil.rmtree(p)
# All own compiled objects are scratch; checked copies now live in retained cache.
for p in b.rglob('NEW_*'):
 if p.is_file() and any(p.name.endswith(s)for s in ['.olean','.olean.private','.olean.server','.ilean']):
  removed.append(dict(path=str(p),kind='compiled-scratch'));p.unlink()
# Nested module files have non-prefixed basenames, e.g. NEW_InverseActual/Funs.olean.
for item in proofs:
 mod=Path(item['module'].replace('.','/'))
 for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
  p=b/(str(mod)+suffix)
  if p.is_file():removed.append(dict(path=str(p),kind='compiled-scratch'));p.unlink()
tmp=b/'NEW_tmp'
if tmp.exists():
 for p in tmp.rglob('*'):
  if p.is_file() and ((p.name.startswith('external-sat')and p.suffix=='.cnf')or p.name.startswith('smt2_dec_problem')):
   removed.append(dict(path=str(p),kind='owned-solver-temp',bytes=p.stat().st_size));p.unlink()
print(json.dumps(dict(exports=exports,removed=removed,retained_cache=str(c),cache_never_deleted=True,shared_tmp_untouched=True,formal_runs=0)))
'''
r=ssh(a,'python3',code);assert r.returncode==0,r.stderr
(E/'NEW_FINAL_CACHE.json').write_text(r.stdout)
print('Exported and cleaned owned scratch')
