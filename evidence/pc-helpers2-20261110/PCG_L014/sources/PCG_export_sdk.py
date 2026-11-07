from pathlib import Path
import hashlib,json,shutil
B=Path.cwd();C=B.parent/'codex-pc-helpers2-cache-20261110';D=C/'PCG_SDK_exports_20261110';D.mkdir(exist_ok=True)
files=[]
for stem in ['PCG_SdkPda','PCG_COMBINED_IMPORT']:
 for p in (B/'PCG_objects').glob(stem+'.*'):
  if not p.is_file():continue
  q=D/p.name;h=hashlib.sha256(p.read_bytes()).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  else:shutil.copyfile(p,q)
  assert p.stat().st_ino!=q.stat().st_ino
  files.append(dict(path=str(q),source=str(p),sha256=h,bytes=q.stat().st_size))
x=dict(export=str(D),base_cache=str(C),LEAN_PATH=[str(D),str(C)],files=files,imports_manifest_sha256=hashlib.sha256((B/'PCG_IMPORTS.json.xz').read_bytes()).hexdigest())
(B/'PCG_SDK_EXPORT_MANIFEST.json').write_text(json.dumps(x,indent=1)+'\n')
print('Exported SDK packet and matching combined import with all object hashes')
