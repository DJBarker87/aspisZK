from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-prepared-claim-20261105'
# Existing reservation client, copied unchanged from seed setup; no launch here.
code='''from pathlib import Path
import subprocess,json,sys
b=Path(B)
with (b/'NGU_NATIVE_RESERVATION.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NGU_NATIVE_RESERVATION.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NGU_NATIVE_RESERVATION.json').read_text());print(json.dumps(a));sys.exit(0 if r.returncode==0 and a.get('allowed') is True else 78)
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\n'+code,text=True,capture_output=True)
 (E/f'NGU_NATIVE_RESERVATION_{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0 and json.loads(r.stdout)['allowed'] is True:break
 if r.returncode not in [78,255] or retry==10:raise SystemExit(r.returncode)
 time.sleep(60 if r.returncode==255 else 180)
for local,name in [('NGU_frozen.tar.xz','NGU_frozen.tar.xz'),('NGU_KMX.patch','NGU_KMX.patch')]:
 data=(E/local).read_bytes()
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'cat > '+B+'/'+name],input=data,capture_output=True)
  if r.returncode==0:break
  (E/f'NGU_NATIVE_UPLOAD_{local}_{retry}.log').write_bytes(r.stderr)
  if r.returncode!=255 or retry==10:raise SystemExit(r.returncode)
  time.sleep(60)
code='''from pathlib import Path
import tarfile,lzma,hashlib,subprocess,json,io
b=Path(B);s=b/'NGU_src';assert not s.exists(),'no second workspace';s.mkdir()
raw=lzma.decompress((b/'NGU_frozen.tar.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==expected
with tarfile.open(fileobj=io.BytesIO(raw)) as tf:tf.extractall(s,filter='data')
r=subprocess.run(['git','apply',str(b/'NGU_KMX.patch')],cwd=s,capture_output=True,text=True);assert r.returncode==0,r.stderr
print(json.dumps(dict(bytes=len(raw),sha256=expected,patch=hashlib.sha256((b/'NGU_KMX.patch').read_bytes()).hexdigest(),exit=0)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nexpected='+repr((E/'NGU_frozen.tar.sha256').read_text().strip())+'\n'+code,text=True,capture_output=True)
(E/'NGU_NATIVE_SETUP.json').write_text(r.stdout);(E/'NGU_NATIVE_SETUP.stderr').write_text(r.stderr);print(r.stdout,r.stderr);assert r.returncode==0
