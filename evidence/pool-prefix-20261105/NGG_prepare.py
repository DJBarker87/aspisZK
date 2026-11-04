from pathlib import Path
import sys,json,subprocess,hashlib,base64
E=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(E.parent/'slice-s-compose10-20261104'))
from NFD_frozen_identity import frozen,apply
files=dict(frozen());files.update({n:v.encode() for n,v in json.loads((E.parent/'pool-retdata-20261104/NFO_INCLUDES.json').read_text()).items()})
patch=(E.parent/'pool-retdata2-20261104/NFR_KMX_copy_stubs.patch').read_text();(E/'NGG_KMX_copy_stubs.patch').write_text(patch);apply(files,patch)
code='''from pathlib import Path
import json,base64
b=Path('/home/dombarker/project-offloads/codex-cx-pool-prefix-20261104')
s=b/'NGG_src';s.mkdir(exist_ok=True)
for n,v in json.loads(INPUT).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v))
print(len(list(s.rglob('*'))))
'''.replace('INPUT',repr(json.dumps({n:base64.b64encode(v).decode() for n,v in files.items()})))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NGG_SOURCE_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
