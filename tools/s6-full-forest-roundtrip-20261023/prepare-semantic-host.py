#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/sys.argv[1]
O.mkdir(exist_ok=False)
source=H/'aspis-s6-full-forest-roundtrip-v1'
shutil.copytree(source/'frozen-source',O/'frozen-source')
for n in ['Cargo.toml','frozen-statement-binding.json']:shutil.copyfile(source/n,O/n)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s6-native-full-forest-roundtrip','aspis-s6-native-semantic-projection'))
(O/'src').mkdir()
(O/'src/lib.rs').write_text('''#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::pool_v1::{pair_forest_terminal::*,payment_relation::*,pair_forest_semantic_terminal::r0::Public};
 #[kani::proof]
 fn semantic_public_same_complete_fields() {
  // All three native payload types contain plain integers/arrays only.
  // No enum discriminant, pointer, Box or reference is fabricated.
  let common:PoolV1PairForestTerminalCommonV1=unsafe {core::mem::transmute(kani::any::<[u8;core::mem::size_of::<PoolV1PairForestTerminalCommonV1>()]>())};
  let transfer:PoolV1PrivateTransferPublicV1=unsafe {core::mem::transmute(kani::any::<[u8;core::mem::size_of::<PoolV1PrivateTransferPublicV1>()]>())};
  let withdrawal:PoolV1WithdrawalPublicV1=unsafe {core::mem::transmute(kani::any::<[u8;core::mem::size_of::<PoolV1WithdrawalPublicV1>()]>())};
  let which:bool=kani::any();
  let statement=if which {PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public:transfer}}
                else {PoolV1PairForestTerminalStatementV1::Withdrawal{common,public:withdrawal}};
  let selected=statement.semantic_public();
  match (&statement,selected) {
   (PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public},Public::Transfer(payment,transition))=>{
    assert!(core::ptr::eq(public,payment));
    assert!(core::ptr::eq(&common.lane_transition,transition));
    kani::cover!(true);
   },
   (PoolV1PairForestTerminalStatementV1::Withdrawal{common,public},Public::Withdrawal(payment,transition))=>{
    assert!(core::ptr::eq(public,payment));
    assert!(core::ptr::eq(&common.lane_transition,transition));
    kani::cover!(true);
   },
   _=>panic!("semantic variant changed"),
  }
 }
}
''')
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'source-manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Actual native semantic_public, complete original payloads and both variants, no child stubs/canonicality restriction. Pointer identity binds every payment and lane-transition field to SAME statement. Does not bind decoder/account/first native execution or prove full forest roundtrip.'),indent=2)+'\n')
print(O)
