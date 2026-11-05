from pathlib import Path
import json,hashlib,shutil,subprocess
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-verify-observed3-20261106')
for name,pin in json.loads((B/'NIH_NHR_INPUT_PINS.json').read_text()).items():
 src=P/name;assert hashlib.sha256(src.read_bytes()).hexdigest()==pin['sha256'],name
 shutil.copyfile(src,B/name)
r=subprocess.run(['python3','NHR_stage.py','--check','--workspace','NHR_workspace','--out','NIH_preflight'],cwd=B)
assert r.returncode==0
r=subprocess.run(['python3','NHR_stage.py','--options','--function','prepare','--workspace','NHR_workspace','--opacity','NIH_OPACITY.json','--out','NIH_options'],cwd=B)
assert r.returncode==0
