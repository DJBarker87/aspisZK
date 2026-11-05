from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-pool-leaves-20261105';C='/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104';H='dombarker@100.108.41.90'
code='''from pathlib import Path
import json,hashlib,os,shutil
b=Path(B);c=Path(C)
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for buf in iter(lambda:f.read(1048576),b''):h.update(buf)
 return h.hexdigest()
active=[]
for d in Path('/proc').iterdir():
 if not d.name.isdigit() or int(d.name)==os.getpid():continue
 try:cmd=(d/'cmdline').read_bytes().replace(b'\\0',b' ').decode(errors='replace');cwd=os.readlink(d/'cwd')
 except OSError:continue
 if B in cmd or cwd==B or cwd.startswith(B+'/'):active.append(dict(pid=int(d.name),cmd=cmd,cwd=cwd))
assert not active,active
x=json.loads((b/'NHC_EXPORT.json').read_text())
for r in x['exports']:
 p=Path(r['path']);assert p.is_file() and digest(p)==r['sha256'] and p.stat().st_size==r['bytes']
removed=[];target_pins=[]
for name in ['NHC_target','NHC_extract_target','NHC_objects','NHC_native']:
 root=b/name
 if not root.exists():continue
 files=[p for p in root.rglob('*') if p.is_file()]
 if name in ['NHC_target','NHC_extract_target']:
  for p in files:
   if p.name.endswith(('.out','.kani-metadata.json')):target_pins.append(dict(path=str(p),sha256=digest(p),bytes=p.stat().st_size,association='current retained target inventory only; no historical-attempt association inferred'))
 else:
  pins={r['source']:r for r in x['exports']}
  assert all(str(p) in pins and digest(p)==pins[str(p)]['sha256'] for p in files)
 removed.append(dict(path=str(root),files=len(files),bytes=sum(p.stat().st_size for p in files)));shutil.rmtree(root)
cache_files=[p for p in c.rglob('*') if p.is_file()]
result=dict(active_owned_provers=active,removed_own_rebuildable=removed,cache_retained=C,cache_files=len(cache_files),cache_bytes=sum(p.stat().st_size for p in cache_files),exports_retained=len(x['exports']),native_target_inventory=target_pins,source_workspace_retained=True,cache_files_deleted=0,wallet_or_key_operations=False,shipped_source_changed=False,release_elf_rebuilt=False)
(b/'NHC_HOST_END.json').write_text(json.dumps(result,indent=1)+'\\n');print(json.dumps(dict(cache_bytes=result['cache_bytes'],removed=removed,exports=len(x['exports']))))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\n'+code,text=True,capture_output=True);(E/'NHC_HOST_END.log').write_text(r.stdout+r.stderr);print(r.stdout[-1600:],r.stderr[-900:]);assert r.returncode==0,r.returncode
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/NHC_HOST_END.json'],capture_output=True);assert r.returncode==0;(E/'NHC_HOST_END.json').write_bytes(r.stdout)
