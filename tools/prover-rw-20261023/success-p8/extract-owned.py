"""Owned safe control references, with actual arithmetic leaves kept explicit."""
from pathlib import Path
import os,subprocess,sys
r=Path(__file__).resolve().parents[3];owner=sys.argv[1]
assert owner in ['polynomial_owned','all_slots_clear','compression_single_state']
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','aspis_core','--opaque','aspis_statement','--start-from','crate::'+owner]
if owner=='polynomial_owned':cmd+=['--include','crate::polynomial_block']
if owner=='all_slots_clear':cmd+=['--include','crate::shipped_pole::equal']
if owner=='compression_single_state':cmd+=['--include','crate::compression_step']
for x in ['aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::PreparedQm31Multiplier']:
 cmd+=['--include',x]
cmd+=['--dest-file',str(r/('PV_P8_'+owner+'.llbc')),'--','--manifest-path',str(Path(__file__).with_name('proof')/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
