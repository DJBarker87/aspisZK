"""One named unchanged native helper, with the pinned extraction toolchain."""
from pathlib import Path
import os,subprocess,sys
r=Path(__file__).resolve().parents[3]
owner=sys.argv[1]
entries={'powers':'crate::weights::powers','ordinary':'crate::sampler::ordinary_sample','gamma':'crate::sampler::gamma_sample','circle':'crate::sampler::circle_sample','mask':'aspis_core::state_only_hiding::state_only_selected_mask_value'}
assert owner in entries
entry=entries[owner]
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_core','--opaque','aspis_statement','--start-from',entry,'--include',entry]
if owner=='powers':cmd+=['--start-from','core::option::Option','--include','core::option::Option']
if owner in ['ordinary','gamma']:cmd+=['--include','crate::sampler::low_base_p_digits','--include','crate::sampler::decode8','--include','crate::sampler::add_small_base_p']
for x in ['aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::wide_exact::WideExact','aspis_core::circle::SecureCirclePoint','aspis_core::r0_transcript::CircleRow']:
 cmd+=['--include',x]
cmd+=['--dest-file',str(r/('ProverRwP6Current'+owner+'.llbc')),'--','--manifest-path',str(r/'crates/aspis-r1-cost-probe/Cargo.toml'),'--features','optimized-terminal,ct-host-prover','--offline','--release','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
