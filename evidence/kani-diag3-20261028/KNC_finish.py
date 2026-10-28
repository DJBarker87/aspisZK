from KNC_host import *
# Read-only recovery of exact captured inputs before deleting own rebuildable outputs.
r=py(f'''from pathlib import Path
import json,zlib,base64
b=Path({B!r});out={{}}
for a in ['KNC_K001','KNC_K002','KNC_K003','KNC_K004']:
 p=b/a/'sources'
 out[a]={{str(f.relative_to(p)):f.read_text() for f in p.rglob('*') if f.is_file()}}
print(base64.b64encode(zlib.compress(json.dumps(out).encode())).decode())
''')
assert r.returncode==0,r.stderr
out=json.loads(zlib.decompress(base64.b64decode(r.stdout)))
index={}
for a,files in out.items():
 index[a]={}
 for n,s in files.items():
  dest=E/'KNC_snapshots'/a/('KNC_'+n.replace('/','__')+'.txt')
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(s)
  index[a][n]=dict(snapshot=str(dest.relative_to(E)),sha256=hashlib.sha256(s.encode()).hexdigest())
(E/'KNC_snapshot_index.json').write_text(json.dumps(index,indent=2)+'\n')
r=py(f'''from pathlib import Path
import json,hashlib,shutil,subprocess
b=Path({B!r});cache=Path('/home/dombarker/project-offloads/codex-cx-kdiag3-cache-20261028')
out={{'removed':[],'retained_cache':str(cache),'shared_kmy_cache_untouched':True,'query_seed_read_only':True}}
for rel in ['KNC_target','KNC_src/target','KNC_tmp']:
 p=b/rel
 if p.exists():
  assert not p.is_symlink(),str(p)
  out['removed'].append(str(p));shutil.rmtree(p)
assert cache.is_dir()
out['kani_binaries']={{}}
for p in Path('/home/dombarker/.kani').glob('kani-0.67.0*/bin/*'):
 if p.is_file() and p.name in ['kani','cbmc','cadical','goto-instrument','kani-compiler']:
  out['kani_binaries'][str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
  if p.name=='cbmc':out['cbmc_version']=subprocess.run([str(p),'--version'],text=True,capture_output=True).stdout.strip()
out['disk_free_bytes']=shutil.disk_usage(b).free
print(json.dumps(out,indent=2))
''')
assert r.returncode==0,r.stderr
(E/'KNC_CLEANUP.json').write_text(r.stdout)
