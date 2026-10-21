from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit20-20261021')
p=H/'src/crates/aspis-r1-cost-probe/src/r1_wire.rs';s=p.read_text()
p.write_text(s[:s.index('#[cfg(kani)]\nmod fields_kani20')]+(H/'harness/fields-kani20.rs').read_text())
