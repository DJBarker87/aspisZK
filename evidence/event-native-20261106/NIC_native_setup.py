"""Own cache seed only; no shared infrastructure mutations."""
from pathlib import Path
import subprocess,json,time,lzma
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-event-native-20261106'
C='/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NIC_20261106'
paths=json.loads(Path('evidence/event-realize-20261106/NIA_RESTORE_PATHS.json').read_text())
seeds={
 'NIA_exports_20261106':'/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NIA_20261106/NIA_exports_20261106',
 'NHZ_exports_20261106':'/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NHZ_20261106/NHZ_exports_20261106',
 'NGK_exports_20261105':'/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NGK_exports_20261105'}
roots=[B+'/NIC_objects']+[C+'/'+k for k in seeds]+paths
roots=list(dict.fromkeys(roots))
(E/'NIC_PATHS.json').write_text(json.dumps(roots,indent=1)+'\n')
def ssh(code):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
  with (E/'NIC_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(stage='setup',retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if retry<10:time.sleep(60)
 raise RuntimeError('transport exhausted')
for retry in range(11):
 r=ssh(f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True);p=b/'NIC_NATIVE_SETUP-admission.json'
with (b/'NIC_NATIVE_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/f'NIC_NATIVE_SETUP-barrier-{retry}.log').write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise
 (E/'NIC_NATIVE_SETUP-admission.json').write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise RuntimeError('admission refused')
r=ssh(f'''from pathlib import Path
import shutil,hashlib,json,lzma
b=Path({B!r});src=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul5-20261029/NFC_src');dst=b/'NIC_src'
assert not dst.exists()
shutil.copytree(src,dst,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
f=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul7-20261029/NFF_FROZEN.json')
x=json.loads(f.read_text());shutil.copy2(f,b/'NIC_FROZEN.json')
for n,t in x.items():
 p=dst/n
 if p.is_file():p.write_text(t)
print(json.dumps(dict(source=str(src),files=sum(p.is_file() for p in dst.rglob('*')),bytes=sum(p.stat().st_size for p in dst.rglob('*') if p.is_file()),frozen_sha256=hashlib.sha256(f.read_bytes()).hexdigest())))
''')
assert r.returncode==0,r.stderr
(E/'NIC_NATIVE_SETUP.json').write_text(r.stdout)
print(r.stdout)
