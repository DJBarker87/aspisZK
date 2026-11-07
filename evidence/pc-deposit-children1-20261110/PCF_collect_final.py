from pathlib import Path
import subprocess,sys,json,hashlib,shutil,lzma
B=Path.cwd();C=B.parent/'codex-pc-deposit-children1-cache-20261110'
subprocess.run([sys.executable,'PCF_collect_artifacts.py'],check=True)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
objs=[]
for p in sorted((B/'PCF_objects').rglob('*')):
 if p.is_file():
  rel=str(p.relative_to(B/'PCF_objects'));assert rel.startswith('PCF_'),rel
  objs.append(dict(module_file=rel,source=str(p),sha256=sha(p),bytes=p.stat().st_size))
key=hashlib.sha256(json.dumps(objs,sort_keys=True).encode()).hexdigest()[:12]
D=C/('PCF_exports_20261110_'+key);D.mkdir(exist_ok=True)
for v in objs:
 p=Path(v['source']);q=D/v['module_file'];q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==v['sha256']
 else:shutil.copyfile(p,q)
 assert sha(q)==v['sha256'];v['export_path']=str(q)
source_pins=[]
for p in sorted((B/'PCF_generated').rglob('*.lean')):
 if p.name!='':source_pins.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
x=dict(export_directory=str(D),lean_path=[str(D),str(C)],files=objs,sources=source_pins,seed_manifest=str(B/'PCF_IMPORTS.json.xz'),seed_manifest_sha256=sha(B/'PCF_IMPORTS.json.xz'),imported_file_count=len(json.loads(lzma.decompress((B/'PCF_IMPORTS.json.xz').read_bytes()))),copy_only=True,hardlinks=False,deletions=0,cache_retained=True,all_export_hashes_verified=True,host_free_bytes=shutil.disk_usage(B).free)
(B/'PCF_EXPORT.json').write_text(json.dumps(x,indent=1)+'\n');(D/'PCF_EXPORT.json').write_text(json.dumps(x,indent=1)+'\n')
print(json.dumps(dict(export_directory=str(D),object_files=len(objs),all_export_hashes_verified=True,host_free_bytes=x['host_free_bytes'],deletions=0)))
