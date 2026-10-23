#!/usr/bin/env python3
"""Focused actual QM31 sampler control, with primitive integer arithmetic."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_core','--start-from','crate::sampler::qm31_sample','--include','crate::sampler','--include','aspis_core::field','--dest-file',str(R/'ProverRwSampler.llbc'),'--','--manifest-path',str(R/'crates/aspis-r1-cost-probe/Cargo.toml'),'--features','optimized-terminal,ct-host-prover','--offline','--release','--lib','--jobs','1']
raise SystemExit(subprocess.run(cmd,cwd=R,env=dict(os.environ,CARGO_TARGET_DIR=str(R.parent/'charon-target'))).returncode)
