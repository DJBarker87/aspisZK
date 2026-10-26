"""Current source extraction for one successful-body owner; no native rewrite."""
from pathlib import Path
import subprocess,sys,os
r=Path(__file__).resolve().parents[3]
owner=sys.argv[1];assert owner in ['ct_pole','sampler','weights','host_work','r1_wire','error-eq','core-scalar']
entry='{impl core::cmp::PartialEq for crate::r1_wire::Error}' if owner=='error-eq' else ('{impl aspis_core::r0::scalar::CodeField for aspis_core::field::wide_exact::WideExact}' if owner=='core-scalar' else 'crate::'+owner)
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_core','--opaque','aspis_statement','--start-from',entry,'--include',('crate::r1_wire::_' if owner=='error-eq' else ('aspis_core::r0::scalar::_' if owner=='core-scalar' else entry))]
if owner=='error-eq':cmd+=['--start-from','crate::r1_wire']
if owner=='core-scalar':cmd+=['--start-from','aspis_core']
for name in ['aspis_core::field::QM31','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::wide_exact::WideExact','aspis_core::circle::SecureCirclePoint','aspis_core::r0_transcript::CircleRow','crate::transport::Variant','crate::verifier::Error','crate::r1_wire::Error']:
 cmd+=['--include',name]
cmd+=['--dest-file',str(r/('ProverRwSuccess'+owner+'.llbc')),'--','--manifest-path',str(r/'crates/aspis-r1-cost-probe/Cargo.toml'),'--features','optimized-terminal,ct-host-prover','--offline','--release','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
