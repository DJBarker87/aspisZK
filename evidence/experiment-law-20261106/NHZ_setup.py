"""Own cache seed only; no shared infrastructure mutations."""
from pathlib import Path
import subprocess,json,time,lzma
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-experiment-law-20261106'
C='/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NHZ_20261106'
paths=json.loads(Path('evidence/prepared-close-20261106/NHS_RESTORE_PATHS.json').read_text())
seeds={
 'NGS_exports_20261105':'/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NGS_exports_20261105',
 'NGR_exports_20261105':'/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NGR_exports_20261105',
 'NGP_exports_20261105':'/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NGP_exports_20261105',
 'NGK_exports_20261105':'/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NGK_exports_20261105',
 'NHK_exports_20261106':'/home/dombarker/project-offloads/codex-cx-transcript-queries-cache-20261104/NHK_exports_20261106',
 'NHS_exports_20261106':'/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NHS_exports_20261106'}
roots=[B+'/NHZ_objects']+[C+'/'+k for k in seeds]+paths
roots=list(dict.fromkeys(roots))
(E/'NHZ_PATHS.json').write_text(json.dumps(roots,indent=1)+'\n')
def ssh(code):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
  with (E/'NHZ_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(stage='setup',retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if retry<10:time.sleep(60)
 raise RuntimeError('transport exhausted')
for retry in range(11):
 r=ssh(f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True);p=b/'NHZ_SETUP-admission.json'
with (b/'NHZ_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/f'NHZ_SETUP-barrier-{retry}.log').write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise
 (E/'NHZ_SETUP-admission.json').write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise RuntimeError('admission refused')
r=ssh(f'''from pathlib import Path
import shutil,hashlib,json,lzma
b=Path({B!r});c=Path({C!r});c.mkdir(exist_ok=True);rows=[]
for name,root in {seeds!r}.items():
 for p in sorted(Path(root).rglob('*')):
  if not p.is_file() or not any(p.name.endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):continue
  dst=c/name/p.relative_to(root);dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists():shutil.copy2(p,dst)
  sha=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(dst.read_bytes()).hexdigest()==sha
  rows.append(dict(source=str(p),path=str(dst),bytes=dst.stat().st_size,sha256=sha))
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copy2('/home/dombarker/project-offloads/codex-cx-prepared-close-20261106/'+n,b/n)
for n in ['NHZ_objects','NHZ_generated','NHZ_native','NHZ_tmp']:(b/n).mkdir(exist_ok=True)
raw=json.dumps(rows).encode();(b/'NHZ_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw))
print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows),manifest_sha256=hashlib.sha256(raw).hexdigest(),rows=rows)))
''')
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);raw=json.dumps(x.pop('rows')).encode();(E/'NHZ_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(E/'NHZ_SETUP.json').write_text(json.dumps(x,indent=1));print(x)
