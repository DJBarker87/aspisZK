from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import subprocess,json,shutil,hashlib,lzma,sys
b=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry-20261105');c=b.parent/'codex-cx-slice-d-entry-cache-20261104';src=b.parent/'codex-cx-ledger8-cache-20261104'
with (b/'NGL_SUPPLEMENT-barrier.log').open('w') as f:r=subprocess.run(['python3',str(b.parent/'codex-cx-s2h-20261023/S2H_reservation.py'),str(b/'NGL_SUPPLEMENT-admission.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NGL_SUPPLEMENT-admission.json').read_text());print(json.dumps(dict(exit=r.returncode,allowed=a.get('allowed'))),flush=True)
if r.returncode or a.get('allowed') is not True:sys.exit(78)
out=[]
for folder in ['NGJ_exports_20261105','NGJ_d_fallback']:
 for p in (src/folder).rglob('*'):
  if not p.is_file():continue
  q=c/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():shutil.copy2(p,q)
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  out.append(dict(source=str(p),destination=str(q),sha256=h,bytes=p.stat().st_size))
raw=json.dumps(out).encode();(b/'NGL_SUPPLEMENT.json.xz').write_bytes(lzma.compress(raw));(b/'NGL_SUPPLEMENT.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n');print(json.dumps(dict(files=len(out),bytes=sum(x['bytes'] for x in out))))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);(E/'NGL_SUPPLEMENT.log').write_text(r.stdout+r.stderr);print(r.stdout);assert r.returncode==0,r.stderr
for n in ['NGL_SUPPLEMENT.json.xz','NGL_SUPPLEMENT.json.sha256','NGL_SUPPLEMENT-admission.json','NGL_SUPPLEMENT-barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat /home/dombarker/project-offloads/codex-cx-slice-d-entry-20261105/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
