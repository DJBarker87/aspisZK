from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-multiproof4-20261108'
code=f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});x=json.loads((b/'NJV_EXPORT.json').read_text())
for f in x['files']:
 p=Path(f['path']);assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256']
free_before=shutil.disk_usage(b).free;removed=[]
for name in ['NJV_target','NJV_objects','NJV_native/NJV_Driver','NJV_native/NJV_ProofDriver']:
 p=b/name;assert not p.is_symlink(),p
 if not p.exists():continue
 size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file()) if p.is_dir() else p.stat().st_size
 if p.is_dir():shutil.rmtree(p)
 else:p.unlink()
 removed.append(dict(path=str(p),bytes=size))
assert Path(x['export']).is_dir()
out=dict(export_hashes_rechecked=True,removed=removed,free_before=free_before,free_after=shutil.disk_usage(b).free,cache_retained=x['cache'],seed_retained=True,wallet_key_operations=False,scope='owned rebuildable target/objects/audit executables only; no source/cache/key/shared path removed')
(b/'NJV_CLEANUP.json').write_text(json.dumps(out,indent=2)+'\\n');print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NJV_CLEANUP.json').write_text(json.dumps(x,indent=2)+'\n');print('NJV cleanup: hash-verified export retained; removed '+str(sum(p['bytes'] for p in x['removed']))+' owned rebuildable bytes; cache/keys untouched')
