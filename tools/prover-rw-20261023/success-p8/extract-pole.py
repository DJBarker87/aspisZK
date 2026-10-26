"""Extract unchanged pole leaves/control using the pinned tools."""
from pathlib import Path
import os,subprocess,sys
r=Path(__file__).resolve().parents[3];owner=sys.argv[1]
assert owner in ['keep_clear','all_slots_clear']
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_core','--start-from','crate::ct_pole::'+owner,'--include','crate::ct_pole::'+owner,'--include','crate::ct_pole::equal']
if owner=='all_slots_clear':cmd+=['--include','crate::ct_pole::keep_clear']
for x in ['aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31']:
 cmd+=['--include',x]
cmd+=['--dest-file',str(r/('PV_Pole_'+owner+'.llbc')),'--','--manifest-path',str(r/'crates/aspis-r1-cost-probe/Cargo.toml'),'--features','optimized-terminal,ct-host-prover','--release','--offline','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
