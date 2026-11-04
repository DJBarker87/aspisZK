"""Frozen source transport once; own scratch only, no shared workspace writes."""
from pathlib import Path
import subprocess,json,lzma,hashlib,base64
E=Path(__file__).resolve().parent;P=E.parent/'slice-s-compose10-20261104'
for n in ['run.py']:
 p=E/('NFJ_'+n);p.write_text(p.read_text().replace('compose11-cache-20261104','compose12-cache-20261104'))
# Retain every frozen file once, not in each attempt's sources directory.
import sys
sys.path.insert(0,str(P));from NFD_frozen_identity import frozen,apply
files=frozen()
for name,data in [('NFJ_KMX_copy_stubs.patch',subprocess.check_output(['git','show','HEAD:evidence/kani-mitig-20261028/KMX_copy_stubs.patch'])),('NFJ_contract_controls.patch',(P/'NFD_contract_controls.patch').read_bytes())]:
 (E/name).write_bytes(data);apply(files,data.decode())
raw=json.dumps({n:base64.b64encode(v).decode() for n,v in files.items()},sort_keys=True).encode()
(E/'NFJ_FROZEN_INPUT.json.xz').write_bytes(lzma.compress(raw));(E/'NFJ_FROZEN_INPUT.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(E/'NFJ_RUST_SOURCE_PINS.json').write_bytes((P/'NFD_RUST_SOURCE_PINS.json').read_bytes())
(E/'NFJ_FROZEN_GRAPH.json').write_bytes(subprocess.check_output(['git','show','HEAD:evidence/leaf-p6-11-20261027/LPm_frozen_graph.json']))
# Existing lane gate copied as own validation script; all old checks preserved.
s=(P/'NFD_program_kani_gate.py').read_text().replace('NFD_','NFJ_')
s=s.replace("[*S.rglob('NFJ_*.rs'),", "[*S.rglob('NFJ_*.rs'),")
(E/'NFJ_kani_gate.py').write_text(s)
# Source identities per file; scratch patch diff is checked separately.
manifest={n:hashlib.sha256(v).hexdigest() for n,v in files.items()}
(E/'NFJ_FROZEN_SHA256.json').write_text(json.dumps(manifest,indent=1)+'\n')
code='''from pathlib import Path
import json,lzma,hashlib,base64,subprocess,sys
b=Path('/home/dombarker/project-offloads/codex-cx-slice-s-compose12-20261104')
q=b/'NFJ_RUST_SETUP-reservation.json'
with (b/'NFJ_RUST_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
print((b/'NFJ_RUST_SETUP-barrier.log').read_text(),flush=True)
if r.returncode or json.loads(q.read_text()).get('allowed') is not True:sys.exit(78)
s=b/'NFJ_src';assert not s.exists()
s.mkdir()
for n,v in json.loads(lzma.decompress(base64.b64decode(PAYLOAD))).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v))
(b/'NFJ_tmp').mkdir(exist_ok=True)
print('frozen scratch created')
'''.replace('PAYLOAD',repr(base64.b64encode((E/'NFJ_FROZEN_INPUT.json.xz').read_bytes()).decode()))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);(E/'NFJ_RUST_SETUP.log').write_text(r.stdout+r.stderr);print(r.stdout+r.stderr);assert r.returncode==0
