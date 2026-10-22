from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit30-20261022')
p=H/'src/crates/aspis-r1-cost-probe/src/r1_wire.rs'
s=p.read_text().split('\n#[cfg(kani)] pub fn make_kani29')[0]
p.write_text(s+'\n'+(H/'harness/semantic-kani30.rs').read_text())
p=H/'src/crates/aspis-r1-cost-probe/src/sim.rs'
p.write_text(p.read_text().split('#[cfg(kani)]\nmod step_kani29')[0])
(H/'revision.txt').write_text('e78e2c022fddebb3d379963ea09efbca478664a7\n')
