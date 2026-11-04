"""Own frozen scratch, exact KMX mitigation, no shipped source edits."""
from pathlib import Path
import subprocess,json,lzma,hashlib,base64,sys
E=Path(__file__).resolve().parent;P=E.parent/'slice-s-compose10-20261104'
sys.path.insert(0,str(P));from NFD_frozen_identity import frozen,apply
files=dict(frozen())
p=subprocess.check_output(['git','show','HEAD:evidence/kani-mitig-20261028/KMX_copy_stubs.patch'])
(E/'NFO_KMX_copy_stubs.patch').write_bytes(p);apply(files,p.decode())
includes=json.loads((E.parent/'slice-s-compose12-20261104/NFJ_INCLUDES.json').read_text())
(E/'NFO_INCLUDES.json').write_text(json.dumps(includes,indent=1)+'\n')
files.update({n:v.encode() for n,v in includes.items()})
raw=json.dumps({n:base64.b64encode(v).decode() for n,v in files.items()},sort_keys=True).encode()
(E/'NFO_FROZEN_INPUT.json.xz').write_bytes(lzma.compress(raw));(E/'NFO_FROZEN_INPUT.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(E/'NFO_RUST_SOURCE_PINS.json').write_bytes((P/'NFD_RUST_SOURCE_PINS.json').read_bytes())
(E/'NFO_FROZEN_GRAPH.json').write_bytes(subprocess.check_output(['git','show','HEAD:evidence/leaf-p6-11-20261027/LPm_frozen_graph.json']))
manifest={n:hashlib.sha256(v).hexdigest() for n,v in files.items()};(E/'NFO_FROZEN_SHA256.json').write_text(json.dumps(manifest,indent=1)+'\n')
code='''from pathlib import Path
import json,lzma,hashlib,base64,subprocess,sys
b=Path('/home/dombarker/project-offloads/codex-cx-pool-retdata-20261104')
q=b/'NFO_RUST_SETUP-reservation.json'
with (b/'NFO_RUST_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
print((b/'NFO_RUST_SETUP-barrier.log').read_text(),flush=True)
if r.returncode or json.loads(q.read_text()).get('allowed') is not True:sys.exit(78)
s=b/'NFO_src';assert not s.exists();s.mkdir()
for n,v in json.loads(lzma.decompress(base64.b64decode(PAYLOAD))).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v))
(b/'NFO_tmp').mkdir(exist_ok=True)
print('frozen scratch created')
'''.replace('PAYLOAD',repr(base64.b64encode((E/'NFO_FROZEN_INPUT.json.xz').read_bytes()).decode()))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);(E/'NFO_RUST_SETUP.log').write_text(r.stdout+r.stderr);print(r.stdout+r.stderr);assert r.returncode==0
