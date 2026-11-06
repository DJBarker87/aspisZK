from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent
inputs=json.loads((E.parent/'slice-d-pair4-20261107/NIG_BASE_REPAIR_INPUTS.json').read_text())
inputs['crates/aspis-r1-cost-probe/src/lib.rs']='#![cfg_attr(kani,feature(allocator_api))]\n'+inputs['crates/aspis-r1-cost-probe/src/lib.rs']
inputs['crates/aspis-r1-cost-probe/src/weights.rs']+='\n#[cfg(kani)] #[path="NJF_boundary.rs"] mod NJF_boundary;\n'
inputs['crates/aspis-r1-cost-probe/src/NJF_boundary.rs']=(E/'NJF_boundary.rs.txt').read_text()
pins={n:hashlib.sha256(t.encode()).hexdigest() for n,t in inputs.items()}
