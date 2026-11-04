from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import subprocess,json,sys,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-slice-d-checkpoint-20261104');p=b/'NGC_FIXTURES-admission.json'
with(b/'NGC_FIXTURES-barrier.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
a=json.loads(p.read_text());print(json.dumps(dict(allowed=a['allowed'],exit=r.returncode)))
if r.returncode!=0 or a['allowed']is not True:sys.exit(78)
s=b.parent/'codex-cx-slice-d-check-cache-20261104'/'fixtures';c=b.parent/'codex-cx-slice-d-checkpoint-cache-20261104'/'fixtures';c.mkdir(exist_ok=True);pins=[]
for p in s.rglob('*'):
 if p.is_file():
  q=c/p.relative_to(s);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);pins.append(dict(source=str(p),target=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
print(json.dumps(pins))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);(E/'NGC_FIXTURES.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
p=E/'NGC_run.py';s=p.read_text().replace("C+'/NFC_audit_support_20261104',T", "C+'/NFC_audit_support_20261104',C+'/fixtures',T");p.write_text(s)
