#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/sys.argv[1];O.mkdir(exist_ok=False)
source=H/'aspis-s6-native-digest-codec-v2'
shutil.copytree(source/'frozen-source',O/'frozen-source')
for n in ['Cargo.toml','frozen-statement-binding.json']:shutil.copyfile(source/n,O/n)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s6-native-digest-codec','aspis-s6-header-digest-reference'))
reference=json.loads((source/'source-manifest.json').read_text())['reference']
assert reference in (source/'src/lib.rs').read_text()
(O/'src').mkdir();(O/'src/lib.rs').write_text('''#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::poseidon2::Digest;
'''+reference+'''
 #[kani::proof]
 #[kani::stub(aspis_statement::atomic_statement::encode_digest_canonical, reference)]
 #[kani::unwind(2048)]
 fn forest_header_with_checked_reference() {
  use aspis_statement::pool_v1::pair_forest_terminal::{decode_pool_v1_pair_forest_terminal_statement_v1 as decode,encode_pool_v1_pair_forest_terminal_statement_v1 as encode,PoolV1PairForestTerminalStatementV1};
  let original:[u8;1880]=kani::any();let index:usize=kani::any();kani::assume(index<144);
  if let Ok(statement)=decode(&original) {
   kani::cover!(matches!(statement,PoolV1PairForestTerminalStatementV1::PrivateTransfer{..}));
   kani::cover!(matches!(statement,PoolV1PairForestTerminalStatementV1::Withdrawal{..}));
   if let Ok(encoded)=encode(&statement){assert_eq!(encoded[index],original[index]);}
  }
 }
}
''')
(O/'source-manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',reference=reference,reference_sha256=hashlib.sha256(reference.encode()).hexdigest(),predecessor='s6-native-digest-encoder-v2',predecessor_reference_source_sha256=hashlib.sha256((source/'src/lib.rs').read_bytes()).hexdigest(),qualification='Only native digest encoder replaced by the exact complete unrolled implementation already checked equal for every native8-limb input; no opaque/arbitrary output stub. Caller source inventories and reference bytes must match the green predecessor. Remaining native full-forest code unchanged; no assumed whole roundtrip or SDK claim.'),indent=2)+'\n')
print(O)
