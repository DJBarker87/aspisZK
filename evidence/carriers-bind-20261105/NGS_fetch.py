"""Read-only recovery of small metadata artifacts, with recorded transport retries."""
from pathlib import Path
import subprocess,json,base64,time
E=Path(__file__).resolve().parent
names=['NGS_CACHE_IMPORTS.json.xz','NGS_CACHE_IMPORTS.json.sha256','NGS_CLOSURE_PINS.json.xz','NGS_CLOSURE_PINS.json.sha256','NGS_PIN_COMPARISON.json','NGS_EXPORT.json']
code='''from pathlib import Path
import json,base64
b=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-20261105')
print(json.dumps({n:base64.b64encode((b/n).read_bytes()).decode() for n in %r}))
'''%names
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 with (E/'NGS_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(step='fetch',retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
for n,v in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(v))
print(json.dumps(dict(files=len(names))))
