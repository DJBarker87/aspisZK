"""Extract the actual generic coefficient permutation, including D's pinned table."""
from pathlib import Path
import os,subprocess
r=Path(__file__).resolve().parents[3]
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_core','--start-from','crate::transport::_::coefficients','--include','crate::transport::_','--include','crate::transport::TAU','--include','crate::transport::Variant','--include','aspis_core::r0::transport::COEFFICIENT_TO_ROW','--include','aspis_core::r0::transport::order','--include','aspis_core::r0::transport::PAD_ROWS','--include','aspis_core::r0::transport::PADS','--include','aspis_core::r0::transport::PIVOT','--dest-file',str(r/'ProverRwP7Coefficients.llbc'),'--','--manifest-path',str(r/'crates/aspis-r1-cost-probe/Cargo.toml'),'--features','optimized-terminal,ct-host-prover','--offline','--release','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
