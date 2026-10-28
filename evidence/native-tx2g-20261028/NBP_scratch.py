from pathlib import Path
import subprocess,shlex,json,hashlib,tarfile,io
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2g-20261028'
m=json.loads(Path('evidence/leaf-sampler1-20261027/LPk_SOURCE.json').read_text())['file_sha256']
a=subprocess.check_output(['git','archive','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',*m])
with tarfile.open(fileobj=io.BytesIO(a)) as t:
 for f in t.getmembers():
  if f.isfile():assert hashlib.sha256(t.extractfile(f).read()).hexdigest()==m[f.name]
(E/'NBP_SCRATCH_MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
# Admission already recorded by NBP_setup immediately before transport; recheck before extraction.
code='''from pathlib import Path
import subprocess,json,sys
b=Path(%r)
with (b/'NBP_SCRATCH-barrier.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NBP_SCRATCH-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NBP_SCRATCH-reservation.json';print(json.dumps(dict(exit=r.returncode,receipt=p.read_text() if p.exists() else None)))
'''%B
r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(code)],capture_output=True,text=True);(E/'NBP_SCRATCH-admission.json').write_text(r.stdout+r.stderr)
assert r.returncode==0
z=json.loads(r.stdout);assert z['exit']==0 and json.loads(z['receipt'])['allowed'] is True,'wait and retry admission only, never extract'
code='''from pathlib import Path
import tarfile,sys
b=Path(%r)/'NBP_src';assert not b.exists();b.mkdir()
with tarfile.open(fileobj=sys.stdin.buffer,mode='r|') as t:t.extractall(b,filter='data')
'''%B
r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(code)],input=a,capture_output=True)
(E/'NBP_SCRATCH-extraction.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout.decode(),stderr=r.stderr.decode())))
assert r.returncode==0,'recover read-only; never resubmit extraction'
