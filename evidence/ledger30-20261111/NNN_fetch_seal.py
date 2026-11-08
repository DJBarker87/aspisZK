"""Retrieve only own retained metadata; no proof submission."""
from pathlib import Path
import subprocess,json,base64
E=Path(__file__).resolve().parent
code="from pathlib import Path;import json,base64;b=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNN_20261111');print(json.dumps({n:base64.b64encode((b/n).read_bytes()).decode()for n in ['NNN_CLOSURE_PINS.json.xz','NNN_CLOSURE_PINS.json.sha256','NNN_EXPORT.json']}))"
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3','-c',__import__('shlex').quote(code)],capture_output=True,text=True);assert r.returncode==0,r.stderr
for n,b in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(b))
print('Own closure seal and export retrieved')
