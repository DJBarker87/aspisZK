"""Pin SAME unchanged audit binaries across fresh fixtures, loaded scan and ax2."""
from pathlib import Path
import json,hashlib,subprocess,sys,time
E=Path.cwd()
import os
for executable in ["NLN_Driver","NLN_ProofDriver"]:
 assert (E/executable).is_file() and os.access(E/executable,os.X_OK),executable
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
pins={str(p):sha(p) for p in [Path('NLN_Driver'),Path('NLN_ProofDriver')]}
if sys.argv[1]=='scan':
 (E/'NLN_AUDIT1_BINARY_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
 t=time.monotonic();r=subprocess.run(['./NLN_ProofDriver','fixtures'],text=True,capture_output=True)
 (E/'NLN_AUDIT1_FIXTURES.log').write_text(r.stdout+r.stderr);print(r.stdout,flush=True)
 assert r.returncode==0
 (E/'NLN_AUDIT1_FIXTURE_METRICS.json').write_text(json.dumps(dict(command=['./NLN_ProofDriver','fixtures'],exit=r.returncode,wall=time.monotonic()-t,binary_sha256=pins['NLN_ProofDriver']))+'\n')
 command=['./NLN_Driver','scan']
else:
 assert pins==json.loads((E/'NLN_AUDIT1_BINARY_PINS.json').read_text()),'STOP changed audit binary'
 command=['./NLN_ProofDriver','proof0']
r=subprocess.run(command)
assert pins=={str(p):sha(p) for p in [Path(n) for n in pins]},'STOP changed audit binary'
raise SystemExit(r.returncode)
