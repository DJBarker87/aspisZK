"""Sequential focused rebuilds of the exact source-byte carrier prerequisites."""
from pathlib import Path
import json,subprocess,sys,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-2tnv-20261028/resume';pins=json.load(open(E/'source-closure.json'))
modules=[f'JFx_DataProof{i:02}' for i in range(15)]+['JFx_DataCheckpoint00','JFx_NativeBytes']
for a,m in enumerate(modules,int(sys.argv[1])):
 d=pins['modules'][m];s=subprocess.check_output(['git','show',d['revision']+':'+d['path']]);assert hashlib.sha256(s).hexdigest()==d['sha256']
 p=E/(m+'.lean.txt');p.write_bytes(s)
 r=subprocess.run([sys.executable,str(R/'tools/pv-2tnv-20261028/check.py'),str(a),m,str(p.relative_to(R))])
 if r.returncode:sys.exit(r.returncode)
