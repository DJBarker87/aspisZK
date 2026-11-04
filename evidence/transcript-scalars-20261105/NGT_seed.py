from pathlib import Path
import shutil,hashlib,json,tarfile,lzma
B=Path('/home/dombarker/project-offloads/codex-cx-transcript-scalars-20261105');C=Path('/home/dombarker/project-offloads/codex-cx-transcript-scalars-cache-20261104');W=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
C.mkdir(exist_ok=True);(B/'NGT_src').mkdir(exist_ok=True)
with tarfile.open(B/'NGT_FROZEN.tar.xz') as t:t.extractall(B/'NGT_src',filter='data')
for n in ['S2W_run_host.py','S2W_lean_host.py','lean-toolchain','lakefile.toml','lakefile.lean','lake-manifest.json']:
 p=W/n
 if p.is_file():shutil.copy2(p,B/n)
paths=json.loads((B/'NGT_PREDECESSOR_PATHS.json').read_text());records=[]
roots=['/home/dombarker/project-offloads/codex-cx-pool-retarget-cache-20261104/NGK_exports_20261105','/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NGN_exports_20261105','/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NGJ_exports_20261105','/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NFW_exports_20261104']
new=[]
for root in roots:
 src=Path(root);dest=C/src.name;dest.mkdir(exist_ok=True);new.append(str(dest))
 for p in src.rglob('*'):
  if p.is_file():
   q=dest/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q);records.append(dict(source=str(p),path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
paths=[str(B/'NGT_objects')]+new+[p for p in paths if Path(p).exists() and p not in roots and not p.endswith('/NGN_objects')]
(B/'NGT_PATHS.json').write_text(json.dumps(paths,indent=1));(B/'NGT_SEED.json').write_text(json.dumps(dict(files=records,total_bytes=sum(r['bytes'] for r in records)),indent=1))
for n in ['NGT_objects','NGT_generated','NGT_tmp']: (B/n).mkdir(exist_ok=True)
print(json.dumps(dict(files=len(records),bytes=sum(r['bytes'] for r in records))))
