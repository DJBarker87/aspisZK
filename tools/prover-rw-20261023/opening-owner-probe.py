#!/usr/bin/env python3
"""Small shape probe; this never changes the frozen production implementation."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2];P=R/'tools/prover-rw-20261023/opening-owner-probe'
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','aspis_core','--include','crate']
for t in ['aspis_core::r0::wire::FibreOpening','aspis_core::r0::domain::FibreIndex','aspis_core::r0::domain::{FibreIndex}::get','aspis_core::field::wide_exact::WideExact','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31']:
 cmd+=['--include',t]
cmd+=['--dest-file',str(R/'OpeningOwnerProbe.llbc'),'--','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--lib','--jobs','1']
raise SystemExit(subprocess.run(cmd,cwd=R,env=dict(os.environ,CARGO_TARGET_DIR=str(R.parent/'charon-target'))).returncode)
