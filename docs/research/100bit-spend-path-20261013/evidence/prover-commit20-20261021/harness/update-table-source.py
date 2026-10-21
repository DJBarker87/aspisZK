from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit20-20261021')
p=H/'src/crates/aspis-r1-cost-probe/src/sim.rs';s=p.read_text()
p.write_text(s[:s.index('#[cfg(kani)]\nmod table_source20')]+(H/'harness/table-source20.rs').read_text())
