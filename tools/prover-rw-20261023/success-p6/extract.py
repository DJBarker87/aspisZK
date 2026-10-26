"""Reference/current-source extraction only, using the pinned unmodified tools."""
from pathlib import Path
import subprocess,os,sys
r=Path(__file__).resolve().parents[3]; d=Path(__file__).with_name('proof')
owner=sys.argv[1]; assert owner in ['compress','all_slots_clear','wide_bytes','wide_bytes_reference','boundary_reference','wide_bytes_flat']
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','aspis_core','--opaque','aspis_statement','--start-from','crate::'+owner]
if owner=='wide_bytes_reference':cmd+=['--include','crate::write_limb']
if owner=='boundary_reference':cmd+=['--include','crate::sum_step']
if owner=='all_slots_clear':cmd+=['--include','crate::shipped_pole::equal']
if owner=='wide_bytes':cmd+=['--include','aspis_core::field::wide_exact::_::to_le_bytes']
for x in ['aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::wide_exact::WideExact']:
 cmd+=['--include',x]
cmd+=['--dest-file',str(r/('ProverRwP6'+owner+'.llbc')),'--','--manifest-path',str(d/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
