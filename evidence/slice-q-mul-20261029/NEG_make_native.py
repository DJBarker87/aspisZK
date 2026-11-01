from pathlib import Path
import subprocess,json,difflib
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';payload={};patch=[]
mods=[('crates/aspis-r1-cost-probe/src/verifier.rs','\n#[cfg(kani)] #[path="NEG_step.rs"] mod NEG_step;\n'),('crates/aspis-r1-cost-probe/src/fast_dots.rs','\n#[cfg(kani)] #[path="NEG_dot_step.rs"] mod NEG_dot_step;\n'),('crates/aspis-r1-cost-probe/src/lib.rs','\n#[cfg(kani)] pub(crate) mod NEG_copy { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }\n')]
for path,addition in mods:
 old=subprocess.check_output(['git','show',F+':'+path],text=True);new=old+addition
 if path.endswith('/lib.rs'):new=new.replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]')
 payload[path]=new;patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
for name in ['NEG_step.rs','NEG_dot_step.rs']:
 path='crates/aspis-r1-cost-probe/src/'+name;new=(E/name).read_text();payload[path]=new;patch.extend(difflib.unified_diff([],new.splitlines(True),fromfile='/dev/null',tofile='b/'+path))
(E/'NEG_PAYLOAD.json').write_text(json.dumps(payload));(E/'NEG_native.patch').write_text(''.join(patch))
