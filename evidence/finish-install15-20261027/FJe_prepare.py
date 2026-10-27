"""Prepare small source slices, without modifying any shipped source."""
from pathlib import Path
import hashlib,json,sys
P=Path(__file__).resolve().parent; R=P.parents[1]; out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
manifest=[]
def cp(source,dest,prefix=None,suffix=b''):
 raw=(R/source).read_bytes(); selected=raw if prefix is None else raw.split(prefix)[0]
 target=out/dest;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(selected+suffix)
 manifest.append(dict(source=source,source_sha256=hashlib.sha256(raw).hexdigest(),selected_prefix_bytes=len(selected),selected_sha256=hashlib.sha256(selected).hexdigest(),target=dest,target_sha256=hashlib.sha256(selected+suffix).hexdigest(),target_bytes=len(selected+suffix)))
cp('crates/aspis-core/src/field.rs','src/field.rs')
cp('crates/aspis-core/src/field/wide_exact.rs','src/field/wide_exact.rs')
cp('crates/aspis-statement/src/poseidon2.rs','src/poseidon2.rs',b'/// Apply the pinned Poseidon2-M31 permutation in place.')
ref=(P/'FJe_reference.rs').read_bytes()
cp('crates/aspis-statement/src/state_only_poseidon.rs','src/FJe_native.rs',b'#[cfg(test)]\nmod tests {',b'\n'+ref)
(out/'src/lib.rs').write_text('extern crate alloc;\nextern crate self as aspis_core;\npub mod field;\nmod poseidon2;\n#[path="FJe_native.rs"] mod state_only_poseidon;\n')
(out/'Cargo.toml').write_text('[package]\nname="fje-packed-p6"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[profile.dev]\nopt-level=3\noverflow-checks=true\n[profile.release]\nopt-level=3\noverflow-checks=true\n')
(out/'FJe_inputs.json').write_text(json.dumps(manifest,indent=2)+'\n')
(P/'FJe_inputs.json').write_text(json.dumps(manifest,indent=2)+'\n')
