#!/usr/bin/env python3
"""Direct selected 64-byte factory; only the E1 fill operation is supplied."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
for name in ['zero32_kernel_contract','factory64_success_and_zero_nonce','factory64_zero_seed_exhaustion','factory64_os_error']:
 cmd=['timeout','90','cargo','kani','--manifest-path','crates/aspis-prover/Cargo.toml','--features','r0,ct-host-prover','--lib','--exact','--harness','state_only_entropy::prover_rw_kani::'+name,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions']
 subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'factory-kani-v3-'+name,*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation then direct 64-byte selected factory, scripted E1 operation; copied private halves, zero nonce/seed guards, draw count or error propagation; no entropy marginal law'),check=True)
