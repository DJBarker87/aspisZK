#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/sys.argv[1];O.mkdir(exist_ok=False)
source=H/'aspis-s6-native-digest-codec-v2'
shutil.copytree(source/'frozen-source',O/'frozen-source')
for n in ['Cargo.toml','frozen-statement-binding.json']:shutil.copyfile(source/n,O/n)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s6-native-digest-codec','aspis-s6-digest-contract'))
p=O/'frozen-source/crates/aspis-statement/src/atomic_statement.rs';original=p.read_text()
signature='pub fn encode_digest_canonical(digest: &Digest) -> [u8; 32] {'
assert original.count(signature)==1
attr='#[cfg_attr(kani, kani::ensures(|result: &[u8;32]| *result == kani_digest_reference(digest)))]\n'
reference='\n#[cfg(kani)]\nfn kani_digest_reference(d:&Digest)->[u8;32] {let mut b=[0u8;32];\n'+''.join(f'b[{4*i}..{4*i+4}].copy_from_slice(&d[{i}].to_le_bytes());\n' for i in range(8))+'b}\n'
changed=original.replace(signature,attr+signature)+reference;p.write_text(changed)
assert changed.replace(attr,'').removesuffix(reference)==original
(O/'proof-cfg-source-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_file=str(p.relative_to(O)),original_sha256=hashlib.sha256(original.encode()).hexdigest(),proof_cfg_sha256=hashlib.sha256(changed.encode()).hexdigest(),attribute=attr,reference=reference,release_source_unchanged_after_stripping_proof_cfg=True,qualification='Proof-only Kani contract attribute/helper on a private copied dependency. Function body and ordinary release source are unchanged; original function contract is checked before summary use. No production adoption or new release artifact.'),indent=2)+'\n')
(O/'src').mkdir();(O/'src/lib.rs').write_text('''#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::{poseidon2::Digest,atomic_statement::encode_digest_canonical as encode};
 #[kani::proof_for_contract(aspis_statement::atomic_statement::encode_digest_canonical)]
 #[kani::unwind(64)]
 fn digest_encoder_contract() {
  let digest:Digest=unsafe{core::mem::transmute(kani::any::<[u32;8]>())};
  let _=encode(&digest);
 }
 #[kani::proof]
 #[kani::stub_verified(aspis_statement::atomic_statement::encode_digest_canonical)]
 #[kani::unwind(2048)]
 fn forest_header_with_digest_contract() {
  use aspis_statement::pool_v1::pair_forest_terminal::{decode_pool_v1_pair_forest_terminal_statement_v1 as decode_forest,encode_pool_v1_pair_forest_terminal_statement_v1 as encode_forest,PoolV1PairForestTerminalStatementV1};
  let original:[u8;1880]=kani::any();let index:usize=kani::any();kani::assume(index<144);
  if let Ok(statement)=decode_forest(&original) {
   kani::cover!(matches!(statement,PoolV1PairForestTerminalStatementV1::PrivateTransfer{..}));
   kani::cover!(matches!(statement,PoolV1PairForestTerminalStatementV1::Withdrawal{..}));
   if let Ok(encoded)=encode_forest(&statement){assert_eq!(encoded[index],original[index]);}
  }
 }
}
''')
print(O)
