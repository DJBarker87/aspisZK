from pathlib import Path
import subprocess,json,lzma
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-transcript-queries3-20261106'
code=f'''from pathlib import Path
import subprocess,json,hashlib,lzma,shutil,sys
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/'NHK_SETUP-reservation.json'
with (b/'NHK_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING',flush=True)
if r.returncode or not p.exists() or json.loads(p.read_text()).get('allowed') is not True:sys.exit(r.returncode or 78)
old=Path('/home/dombarker/project-offloads/codex-cx-transcript-queries-20261105')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(old/n,b/n)
rows=[]
c=Path('/home/dombarker/project-offloads/codex-cx-transcript-queries-cache-20261104')
for folder in ['NHB_exports_20261105','NHA_exports_20261105','NGQ_exports_20261105','NGQ_final_events_20261105','NGK_exports_20261105','NGP_exports_20261105']:
 for p in sorted((c/folder).rglob('*')):
  if p.is_file():rows.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
raw=json.dumps(rows,indent=1).encode();(b/'NHK_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw))
for n in ['NHK_objects','NHK_generated','NHK_native','NHK_tmp']:(b/n).mkdir(exist_ok=True)
print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows))))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NHK_SETUP.log').write_text(r.stdout+r.stderr);print(r.stdout,r.stderr);assert r.returncode==0,r.returncode
r=subprocess.run(['scp','dombarker@100.108.41.90:'+B+'/NHK_CACHE_IMPORTS.json.xz',str(E)],capture_output=True,text=True);assert r.returncode==0,r.stderr
