import sys
sys.dont_write_bytecode=True
from NDL_sources import source
"""Upload only lane-owned inputs after an accepted reservation, without launching."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
payload={n:source(n) for n in ['NDL_weights.rs','NDL_reference.rs']}
code=r'''from pathlib import Path
import json,subprocess,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-native-front1b-20261028')
with (b/'NDL_UPLOAD-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NDL_UPLOAD-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
print((b/'NDL_UPLOAD-barrier.log').read_text());ad=json.loads((b/'NDL_UPLOAD-reservation.json').read_text());assert r.returncode==0 and ad['allowed'] is True
s=b/'NDL_src'
for n,t in payload.items():(s/'crates/aspis-r1-cost-probe/src'/n).write_text(t)
p=s/'crates/aspis-r1-cost-probe/src/weights.rs';text=p.read_text()
if 'field_exact_post' not in text:
 text=text.replace('pub fn field(bytes:', '#[cfg_attr(all(kani,NDL_exact_field),kani::requires(NDL_weights::field_domain(bytes,i)))]\n#[cfg_attr(all(kani,NDL_exact_field),kani::ensures(|r| NDL_weights::field_exact_post(*r,bytes,i)))]\npub fn field(bytes:')
 p.write_text(text)
x=json.loads((b/'NDL_SOURCE_PINS.json').read_text())
for p in [p,s/'crates/aspis-r1-cost-probe/src/NDL_weights.rs',s/'crates/aspis-r1-cost-probe/src/NDL_reference.rs']:x[str(p.relative_to(s))]=hashlib.sha256(p.read_bytes()).hexdigest()
(b/'NDL_SOURCE_PINS.json').write_text(json.dumps(x))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='payload='+repr(payload)+'\n'+code,text=True,capture_output=True)
(E/'NDL_UPLOAD.log').write_text(r.stdout+r.stderr);print(r.returncode,r.stdout,r.stderr);sys.exit(r.returncode)
