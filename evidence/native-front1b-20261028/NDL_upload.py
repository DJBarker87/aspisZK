import sys
sys.dont_write_bytecode=True
from NDL_sources import source,sources
"""Upload only lane-owned inputs after an accepted reservation, without launching."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
payload={n:source(n) for n in ['NDL_weights.rs','NDL_reference.rs','NDL_core.rs','NDL_core_reference.rs','NDL_dot.rs','NDL_pairing.rs'] if (E/n).exists() or n in sources()}
code=r'''from pathlib import Path
import json,subprocess,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-native-front1b-20261028')
with (b/'NDL_UPLOAD-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NDL_UPLOAD-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
print((b/'NDL_UPLOAD-barrier.log').read_text());ad=json.loads((b/'NDL_UPLOAD-reservation.json').read_text());assert r.returncode==0 and ad['allowed'] is True
s=b/'NDL_src'
for n,t in payload.items():
 p=s/('crates/aspis-core/src/field' if n in ['NDL_core.rs','NDL_core_reference.rs'] else 'crates/aspis-r1-cost-probe/src')/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
if 'NDL_core.rs' in payload:
 p=s/'crates/aspis-core/src/field.rs';t=p.read_text()
 if 'mod NDL_core' not in t:p.write_text(t+'\n#[cfg(kani)]\n#[path="field/NDL_core.rs"] mod NDL_core;\n')
if 'NDL_dot.rs' in payload:
 p=s/'crates/aspis-r1-cost-probe/src/fast_pairing.rs';t=p.read_text()
 if 'mod NDL_dot' not in t:
  t=t.replace('    pub const P:u32=', '    #[cfg(kani)] pub(crate) mod NDL_dot { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/NDL_dot.rs")); }\n    pub const P:u32=')
  assert 'mod NDL_dot' in t
  t+='\n#[cfg(kani)] #[path="NDL_pairing.rs"] pub(crate) mod NDL_pairing;\n';p.write_text(t)

p=s/'crates/aspis-r1-cost-probe/src/weights.rs';text=p.read_text()
if 'field_exact_post' not in text:
 text=text.replace('pub fn field(bytes:', '#[cfg_attr(all(kani,NDL_exact_field),kani::requires(NDL_weights::field_domain(bytes,i)))]\n#[cfg_attr(all(kani,NDL_exact_field),kani::ensures(|r| NDL_weights::field_exact_post(*r,bytes,i)))]\npub fn field(bytes:')
 p.write_text(text)
if 'guard_raw_post(*r,w,folds)' not in text:
 text=text.replace('fn shared_two_point_guard(w:', '#[cfg_attr(all(kani,NDL_guard_raw),kani::ensures(|r| NDL_weights::guard_raw_post(*r,w,folds)))]\nfn shared_two_point_guard(w:');p.write_text(text)
x=json.loads((b/'NDL_SOURCE_PINS.json').read_text())
for p in s.rglob('*.rs'):
 if str(p.relative_to(s)) in x or p.name.startswith('NDL_'):x[str(p.relative_to(s))]=hashlib.sha256(p.read_bytes()).hexdigest()
(b/'NDL_SOURCE_PINS.json').write_text(json.dumps(x))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='payload='+repr(payload)+'\n'+code,text=True,capture_output=True)
(E/'NDL_UPLOAD.log').write_text(r.stdout+r.stderr);print(r.returncode,r.stdout,r.stderr);sys.exit(r.returncode)
