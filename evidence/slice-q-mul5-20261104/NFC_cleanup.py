from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
cgroups=[json.loads(p.read_text())['cgroup'] for p in E.glob('NFC_[LK]*/receipt.json')]
code=f'''from pathlib import Path
import json,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul5-20261029');C=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul5-cache-20261029')
active=[]
for name in {cgroups!r}:
 p=Path(name)/'cgroup.events'
 if p.exists() and 'populated 1' in p.read_text():active.append(name)
assert not active,active
removed=[]
for name in ['NFC_target','NFC_tmp','NFC_objects']:
 p=B/name
 if p.exists():
  assert not p.is_symlink() and p.resolve().parent==B.resolve()
  files=[x for x in p.rglob('*') if x.is_file()];size=sum(x.stat().st_size for x in files)
  shutil.rmtree(p);removed.append(dict(path=str(p),files=len(files),bytes=size))
for name in ['NFC_Driver','NFC_ProofDriver']:
 p=B/'NFC_native'/name
 if p.is_file():removed.append(dict(path=str(p),files=1,bytes=p.stat().st_size));p.unlink()
assert C.is_dir() and (C/'NFC_exports_20261104').is_dir() and (B/'NFC_src').is_dir()
print(json.dumps(dict(all_125_scopes_terminal=True,active_cgroups=active,removed=removed,own_cache_retained=str(C),source_workspace_retained=str(B/'NFC_src'),wallet_or_key_operations=False,qualification='Only own compiler/solver/runtime scratch; no other workspace/cache touched.')))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
(E/'NFC_CLEANUP.json').write_text(r.stdout);print(sum(x['bytes'] for x in json.loads(r.stdout)['removed']),'rebuildable bytes removed; own cache and source workspace retained')
