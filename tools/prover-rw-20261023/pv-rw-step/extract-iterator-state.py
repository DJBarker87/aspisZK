"""Extract one combined actual iterator/arithmetic state transition, with pinned tools."""
from pathlib import Path
import subprocess,os
r=Path(__file__).resolve().parents[3]
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','aspis_core','--opaque','aspis_statement','--start-from','crate::iterator_state_step::iterator_state_step']
for x in ['aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31']:
 cmd+=['--include',x]
cmd+=['--dest-file',str(r/'PV_RW_IteratorStateStep.llbc'),'--','--manifest-path',str(Path(__file__).with_name('proof')/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
