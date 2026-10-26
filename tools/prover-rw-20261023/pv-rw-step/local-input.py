"""Immutable input evidence for a manually launched tiny local Lean check."""
from pathlib import Path
import hashlib,json,sys,subprocess,datetime,re
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw-step-20261026/local';e.mkdir(exist_ok=True)
a=int(sys.argv[1]);module=sys.argv[2];assert 23700<=a<=23999 and module.startswith('PV_RW_')
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(module+'.lean');assert p.is_file()
assert not (e/f'{a}-input.json').exists()
tool=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0');project=r/'docs/research/100bit-spend-path-20261013/evidence/s2d-20261023';cache=Path('/private/tmp/pv-rw-step-local-20261026');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
pins={str(q):sha(q) for q in [tool/'bin/lean',tool/'lib/lean/Std.olean',project/'lakefile.toml',project/'lean-toolchain']}
seen=set()
def visit(name):
 if name in seen or name=='Std':return
 seen.add(name);assert name.startswith('R1Z.PV_RW_')
 q=cache/(name.replace('.','/')+'.olean');assert q.is_file(),q
 pins[str(q)]=sha(q)
 source=r/'docs/research/v8-r0-zk-20261009/lean'/(name.replace('.','/')+'.lean')
 for child in re.findall(r'^import ([\w.]+)',source.read_text(),re.M):visit(child)
for name in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(name)
(e/f'{a}.lean.txt').write_bytes(p.read_bytes())
x=dict(attempt=a,kind='local',module='R1Z/'+module,source_sha256=sha(p),source_snapshot=f'{a}.lean.txt',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()+'+uncommitted-local-proof',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),dependency_pins=pins,deps_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),cwd=str(project),command=['/usr/bin/time','-l','env','LEAN_PATH='+str(cache),'lake','env','lean','-M7000','-R',str(r/'docs/research/v8-r0-zk-20261009/lean'),'-o',str(cache/'R1Z'/(module+'.olean')),str(p)],limits=dict(lean_memory_mb=7000),scope='Small local Std-only focused job under lead(c); no cold dependencies. No cgroup on macOS. Standard compiler/root and own cached inputs pinned; no release replay.')
(e/f'{a}-input.json').write_text(json.dumps(x,indent=2)+'\n');print(x['source_sha256'])
