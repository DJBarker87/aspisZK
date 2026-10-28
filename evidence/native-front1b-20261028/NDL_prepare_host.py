from pathlib import Path
import json,hashlib,subprocess
B=Path('/home/dombarker/project-offloads/codex-cx-native-front1b-20261028')
old=Path('/home/dombarker/project-offloads/codex-cx-native-front1-20261028')
with (B/'NDL_PREP-barrier.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'NDL_PREP-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
print((B/'NDL_PREP-barrier.log').read_text());ad=json.loads((B/'NDL_PREP-reservation.json').read_text());assert r.returncode==0 and ad['allowed'] is True
s=B/'NDL_src'
if not s.exists():s.symlink_to(old/'NDD_src',target_is_directory=True)
p=s/'crates/aspis-r1-cost-probe/src/weights.rs';baseline=p.read_text();(B/'NDL_weights_before.rs').write_text(baseline)
assert 'mod NDL_weights' not in baseline
baseline=baseline.replace('pub fn field(bytes:', '#[cfg_attr(kani,kani::ensures(|r| NDL_weights::field_post(*r)))]\npub fn field(bytes:')
baseline+='\n#[cfg(kani)]\n#[path="NDL_weights.rs"] mod NDL_weights;\n';p.write_text(baseline)
for n,t in payload.items():(s/'crates/aspis-r1-cost-probe/src'/n).write_text(t)
pins=json.loads((old/'NDD_SOURCE_PINS.json').read_text())
for p in [p,s/'crates/aspis-r1-cost-probe/src/NDL_weights.rs',s/'crates/aspis-r1-cost-probe/src/NDL_reference.rs']:pins[str(p.relative_to(s))]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NDL_SOURCE_PINS.json').write_text(json.dumps(pins))
