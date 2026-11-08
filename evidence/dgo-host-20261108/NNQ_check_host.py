"""Read-only verification of accepted overlay objects and selected dependency pins."""
from pathlib import Path
import subprocess, json, time
E=Path(__file__).resolve().parent
pins=json.loads((E/'NNQ_PINS.json').read_text())
expected={x['path']:x['sha256'] for x in pins['inherited_selected_objects']}
for m in pins['modules']:
    x=m['object']; assert expected.get(x['path'],x['sha256'])==x['sha256']; expected[x['path']]=x['sha256']
code='''import hashlib,json
from pathlib import Path
expected=json.loads(INPUT)
for p,h in expected.items():
 assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
print(json.dumps(dict(verified_files=len(expected),shared_workspace_write=False)))
'''.replace('INPUT',repr(json.dumps(expected)))
for retry in range(11):
    r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
    if r.returncode!=255:break
    with (E/'NNQ_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(event='final_readonly_transport_retry',retry=retry,exit=255,stderr=r.stderr))+'\n')
    if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);out['accepted_modules']=len(pins['modules'])
(E/'NNQ_HOST_FINAL_CHECK2.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
