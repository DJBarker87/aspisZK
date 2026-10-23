#!/usr/bin/env python3
"""Small selected-source extraction before enlarging the prover cone."""
from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2]
target=sys.argv[1] if len(sys.argv)>1 else 'round'
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_core','--start-from','crate::prover::'+target,'--include','crate::prover::'+target,'--include','aspis_core::field::wide_exact::WideExact','--include','aspis_core::field::QM31','--include','aspis_core::field::CM31','--include','aspis_core::field::M31','--include','crate::host_commitment::PrivateSalts','--include','crate::weights::PERM','--include','crate::weights::QUARTER','--dest-file',str(R/('ProverRwProbe-'+target+'.llbc')),'--','--manifest-path',str(R/'crates/aspis-r1-cost-probe/Cargo.toml'),'--features','optimized-terminal,ct-host-prover','--offline','--release','--lib','--jobs','1']
raise SystemExit(subprocess.run(cmd,cwd=R).returncode)
