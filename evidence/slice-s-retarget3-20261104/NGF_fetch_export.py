from pathlib import Path
import subprocess,json,base64,lzma,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-retarget3-20261104'
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=f'''from pathlib import Path
import json,base64
b=Path({B!r});print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in ['NGF_EXPORT.json','NGF_CLOSURE_PINS.json.xz','NGF_CLOSURE_PINS.json.sha256']}}))
''',text=True,capture_output=True);assert r.returncode==0,r.stderr
for n,v in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(v))
raw=lzma.decompress((E/'NGF_CLOSURE_PINS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(E/'NGF_CLOSURE_PINS.json.sha256').read_text().strip();print('closure pins verified')
