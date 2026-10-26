"""Extract only the current polynomial control; field owners stay opaque leaves."""
from pathlib import Path
import os,subprocess
r=Path(__file__).resolve().parents[3]
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','aspis_core','--opaque','aspis_statement','--start-from','crate::eval_poly']
for x in ['aspis_core::state_only_sumcheck::evaluate_state_only_polynomial','aspis_core::state_only_sumcheck::evaluate_state_only_polynomial::closure','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::PreparedQm31Multiplier']:
 cmd+=['--include',x]
cmd+=['--dest-file',str(r/'PV_PolyControl.llbc'),'--','--manifest-path',str(r/'tools/prover-rw-20261023/success-p6/direct/Cargo.toml'),'--release','--offline','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
