"""Install job-private cost/count scripts, with pre-upload admission. No gate launches."""
from pathlib import Path
import subprocess,json
P=Path(__file__).resolve().parent;D='/home/dombarker/project-offloads/codex-pv-integ4-20261027'
payload={'scratch/batch1-cost/function-cost.rs':(P/'batch1-function-cost.rs').read_text(),'scratch/batch1-cost/pole_original.rs':subprocess.check_output(['git','show','c57a344726:crates/aspis-r1-cost-probe/src/ct_pole.rs'],text=True)}
payload['scratch/batch1-cost/Cargo.toml']='''[package]
name="pv-integ4-batch1-cost"
version="0.1.0"
edition="2021"
[workspace]
[[bin]]
name="pv-integ4-batch1-cost"
path="function-cost.rs"
[dependencies]
aspis-core={path="../../source/crates/aspis-core",features=["r0"]}
aspis-statement={path="../../source/crates/aspis-statement",features=["r0","pool-v1-kernel"]}
aspis-r1-cost-probe={path="../../source/crates/aspis-r1-cost-probe",features=["optimized-terminal","ct-host-prover"]}
[profile.release]
opt-level=3
[profile.release.package.aspis-r1-cert-check]
overflow-checks=true
[profile.release.package.aspis-r1-cert-build]
overflow-checks=true
'''
# Scratch sits D/scratch/batch1-cost: ../../source selects the exact pinned source.
code=f'''from pathlib import Path
import json,subprocess,hashlib
D=Path({D!r});O=D/'upload-batch1';O.mkdir()
r=subprocess.run(['python3',str(D/'reservation.py'),str(O/'admission.json')],stdout=open(O/'output.log','w'),stderr=subprocess.STDOUT)
assert r.returncode==0 and json.loads((O/'admission.json').read_text())['allowed']
payload={payload!r}
for n,s in payload.items():
 p=D/n;p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists();p.write_text(s)
(O/'input-pins.json').write_text(json.dumps({{n:hashlib.sha256(s.encode()).hexdigest() for n,s in payload.items()}},indent=2))
'''
subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,check=True)
