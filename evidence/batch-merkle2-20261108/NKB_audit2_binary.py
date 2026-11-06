"""Pin SAME unchanged audit binaries across fresh fixtures, loaded scan and ax2."""
from pathlib import Path
import json,hashlib,subprocess,sys,time
E=Path.cwd()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
pins={str(p):sha(p) for p in [Path('NKB_native/NKB_Driver'),Path('NKB_native/NKB_ProofDriver')]}
if sys.argv[1]=='scan':
 (E/'NKB_AUDIT2_BINARY_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
 t=time.monotonic();r=subprocess.run(['NKB_native/NKB_ProofDriver','fixtures'],text=True,capture_output=True)
 (E/'NKB_AUDIT2_FIXTURES.log').write_text(r.stdout+r.stderr);print(r.stdout,flush=True)
 assert r.returncode==0
 (E/'NKB_AUDIT2_FIXTURE_METRICS.json').write_text(json.dumps(dict(command=['NKB_native/NKB_ProofDriver','fixtures'],exit=r.returncode,wall=time.monotonic()-t,binary_sha256=pins['NKB_native/NKB_ProofDriver']))+'\n')
 command=['NKB_native/NKB_Driver','scan']
else:
 assert pins==json.loads((E/'NKB_AUDIT2_BINARY_PINS.json').read_text()),'STOP changed audit binary'
 command=['NKB_native/NKB_ProofDriver','proof0']
r=subprocess.run(command)
assert pins=={str(p):sha(p) for p in [Path(n) for n in pins]},'STOP changed audit binary'
raise SystemExit(r.returncode)
