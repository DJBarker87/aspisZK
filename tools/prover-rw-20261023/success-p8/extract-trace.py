"""Extract the actual selected ct-host-prover trace callback, preserving cfg."""
from pathlib import Path
import os,subprocess
r=Path(__file__).resolve().parents[3]
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_core','--start-from','crate::trace::value','--include','crate::trace::value']
for x in ['aspis_core::field::wide_exact::WideExact','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31']:
 cmd+=['--include',x]
cmd+=['--dest-file',str(r/'PV_TraceValue.llbc'),'--','--manifest-path',str(r/'crates/aspis-r1-cost-probe/Cargo.toml'),'--features','optimized-terminal,ct-host-prover','--release','--offline','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
