"""Run the byte-identical NHR validator in this owned scratch, no extraction."""
from pathlib import Path
import json,base64,subprocess,hashlib,shutil
B=Path(__file__).resolve().parent
for name in ['NHR_stage.py','NHR_STAGING_MANIFEST.json','NHR_FROZEN_PAYLOAD.json.sha256']:
 shutil.copyfile(B/('NHU_'+name+'.txt'),B/name)
(B/'NHR_FROZEN_PAYLOAD.json.xz').write_bytes(base64.b64decode((B/'NHU_FROZEN_PAYLOAD.b64.txt').read_bytes()))
r=subprocess.run(['python3','NHR_stage.py','--check','--workspace','NHU_src','--out','NHU_preflight'],cwd=B)
assert r.returncode==0
# Prescribed patch only: no new or alternative copy implementation.
patch=B/'NHU_KMX.patch'
assert hashlib.sha256(patch.read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
r=subprocess.run(['patch','--batch','-p1','-i',str(patch)],cwd=B/'NHU_src');assert r.returncode==0
out=dict(status='PASS',extraction_runs=0,stager_sha256=hashlib.sha256((B/'NHR_stage.py').read_bytes()).hexdigest(),patch_sha256=hashlib.sha256(patch.read_bytes()).hexdigest(),files=len(json.loads((B/'NHR_STAGING_MANIFEST.json').read_text())['files']))
(B/'NHU_STAGE_REPORT.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
