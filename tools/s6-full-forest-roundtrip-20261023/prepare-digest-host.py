#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/sys.argv[1];O.mkdir(exist_ok=False)
source=H/'aspis-s6-native-semantic-projection-v1'
shutil.copytree(source/'frozen-source',O/'frozen-source')
for n in ['Cargo.toml','frozen-statement-binding.json']:shutil.copyfile(source/n,O/n)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s6-native-semantic-projection','aspis-s6-native-digest-codec'))
(O/'src').mkdir()
reference='fn reference(d:&Digest)->[u8;32] {let mut b=[0u8;32];\n'+''.join(f'b[{4*i}..{4*i+4}].copy_from_slice(&d[{i}].to_le_bytes());\n' for i in range(8))+'b}\n'
proof='''#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::poseidon2::Digest;
 use aspis_statement::atomic_statement::{encode_digest_canonical as encode,decode_digest_canonical as decode};
'''+reference+'''
 #[kani::proof]
 #[kani::unwind(64)]
 fn encoder_matches_unrolled() {
  // Digest is the complete native eight-u32-limb carrier; all bit patterns valid.
  let digest:Digest=unsafe{core::mem::transmute(kani::any::<[u32;8]>())};
  assert_eq!(encode(&digest),reference(&digest));
 }
 #[kani::proof]
 #[kani::unwind(64)]
 fn accepted_digest_roundtrip() {
  let original:[u8;32]=kani::any();
  let result=decode(&original);
  kani::cover!(result.is_ok());
  kani::cover!(result.is_err());
  if let Ok(digest)=result {assert_eq!(encode(&digest),original);}
 }
}
'''
(O/'src/lib.rs').write_text(proof)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'source-manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,reference=reference,qualification='Actual native canonical digest codec, no child stubs. Native loop/unrolled reference equality for all native eight-limb values; separate accepted native decoder/encoder byte roundtrip for arbitrary32 bytes. No whole forest/SDK/Lean port installation claim.'),indent=2)+'\n')
print(O)
