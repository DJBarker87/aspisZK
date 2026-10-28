"""Prepare one owned frozen scratch corpus. No build or scope is launched."""
from pathlib import Path
import json,subprocess,hashlib,tarfile,io,shlex,time
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2a-20261027'
manifest=json.loads(Path('evidence/leaf-sampler1-20261027/LPk_SOURCE.json').read_text())['file_sha256']
archive=subprocess.check_output(['git','archive','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',*manifest])
with tarfile.open(fileobj=io.BytesIO(archive)) as t:
 for m in t.getmembers():
  if m.isfile():assert hashlib.sha256(t.extractfile(m).read()).hexdigest()==manifest[m.name]
(E/'NBC_SCRATCH_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
# Reservation BEFORE any corpus transport, as required by local-lean rule7.
for n in range(11):
 code=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/'NBC_PREP-reservation.json'
with (b/'NBC_PREP-barrier.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(json.dumps(dict(exit=r.returncode,receipt=p.read_text() if p.exists() else None,log=(b/'NBC_PREP-barrier.log').read_text())))
'''
 r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(code)],capture_output=True,text=True)
 (E/f'NBC_PREP-transport-{n}.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr))+'\n')
 if r.returncode==255:
  if n<10:time.sleep(60);continue
  raise SystemExit('transport exhausted')
 assert r.returncode==0,r.stderr
 z=json.loads(r.stdout);ad=json.loads(z['receipt']) if z['receipt'] else None
 if ad and z['exit']==0 and ad.get('allowed') is True:break
 if n==0 and not ad:time.sleep(30);continue
 if ad and (z['exit']==78 or ad.get('allowed') is False) and n<10:time.sleep(180);continue
 raise SystemExit('STOP reservation '+r.stdout)
code=f'''from pathlib import Path
import tarfile,sys
b=Path({B!r})/'NBC_src'
assert not b.exists(),'refuse second scratch creation'
b.mkdir()
with tarfile.open(fileobj=sys.stdin.buffer,mode='r|') as t:t.extractall(b,filter='data')
'''
# Never resubmit an extraction after a submitted transport failure: inspect read-only.
r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(code)],input=archive,capture_output=True)
(E/'NBC_PREP-extraction.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout.decode(),stderr=r.stderr.decode()))+'\n')
assert r.returncode==0,'recover extraction read-only, do not rerun'
