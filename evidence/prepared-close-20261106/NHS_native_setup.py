from pathlib import Path
import json,subprocess,time,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-prepared-close-20261106';H='dombarker@100.108.41.90'
def ssh(code,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
  with (E/'NHS_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(step='native_setup',retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Recover submitted setup read-only; never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('transport exhausted')
for retry in range(11):
 r=ssh(f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});p=b/'NHS_NATIVE_SETUP-admission.json'
with (b/'NHS_NATIVE_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/f'NHS_NATIVE_SETUP-barrier-{retry}.log').write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('missing admission')
 (E/'NHS_NATIVE_SETUP-admission.json').write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise RuntimeError('admission refused')
u=json.loads((E/'NHS_NATIVE_UPLOAD.json').read_text());pins=json.loads((E/'NHS_SOURCE_PINS.json').read_text())
r=ssh(f'''from pathlib import Path
import shutil,json,hashlib
b=Path({B!r});s=b/'NHS_src';origin=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-20261105/NGN_src')
assert not s.exists(),'setup already exists: inspect read-only'
shutil.copytree(origin,s)
for n,t in json.loads({json.dumps(u)!r}).items():(s/n).write_text(t)
pins=json.loads({json.dumps(pins)!r})
errors=[n for n,h in pins.items() if not (s/n).is_file() or hashlib.sha256((s/n).read_bytes()).hexdigest()!=h]
assert not errors,errors
print(json.dumps(dict(files=len(pins),bytes=sum(p.stat().st_size for p in s.rglob('*') if p.is_file()),errors=errors,source_origin=str(origin),frozen_lock=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),disk_free=shutil.disk_usage(s).free)))
''',submitted=True)
(E/'NHS_NATIVE_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr+r.stdout
print(r.stdout)
