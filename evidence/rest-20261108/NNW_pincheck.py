"""Read-only postcheck of every imported direct/Aeneas object pinned by this job."""
from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent
pins={}
for p in E.glob('NNW_L[0-9][0-9][0-9]/receipt.json'):
 for path,v in json.loads(p.read_text())['deps_fingerprint']['selected_objects'].items():
  if path in pins:assert pins[path]['sha256']==v['sha256'],path
  pins[path]=v
code='''import json,hashlib,pathlib,sys
pins=json.loads(sys.stdin.read());bad=[]
for p,v in pins.items():
 z=pathlib.Path(p)
 if not z.is_file() or hashlib.sha256(z.read_bytes()).hexdigest()!=v['sha256']:bad.append(p)
print(json.dumps(dict(selected_objects=len(pins),changed_paths=bad)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3 -c '+__import__('shlex').quote(code)],input=json.dumps(pins),text=True,capture_output=True)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);assert not out['changed_paths'],out
for n,v in json.loads((E/'NNW_INPUT_PINS.json').read_text()).items():assert hashlib.sha256(Path(v['path']).read_bytes()).hexdigest()==v['sha256']
(E/'NNW_PINCHECK.json').write_text(json.dumps(out,indent=2)+'\n')
print(r.stdout)
