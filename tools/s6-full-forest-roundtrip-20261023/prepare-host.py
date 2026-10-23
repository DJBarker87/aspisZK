#!/usr/bin/env python3
from pathlib import Path
import shutil,json,hashlib,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
O=H/sys.argv[1];O.mkdir(exist_ok=False)
source=H/'aspis-s1-claim-borrowed-step-v1'
shutil.copytree(source/'frozen-source',O/'frozen-source')
shutil.copyfile(source/'frozen-statement-binding.json',O/'frozen-statement-binding.json')
(O/'src').mkdir()
(O/'Cargo.toml').write_text('''[package]
name="aspis-s6-native-full-forest-roundtrip"
version="0.0.0"
edition="2021"
[workspace]
exclude=["frozen-source/crates/aspis-statement"]
[dependencies]
aspis-statement={path="frozen-source/crates/aspis-statement",features=["r0"]}
[profile.release]
opt-level=3
overflow-checks=true
''')
(O/'src/lib.rs').write_text('''#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::pool_v1::pair_forest_terminal::{
  decode_pool_v1_pair_forest_terminal_statement_v1 as decode,
  encode_pool_v1_pair_forest_terminal_statement_v1 as encode};
 #[kani::proof]
 #[kani::unwind(2048)]
 fn accepted_common_header_roundtrip() {
  let original:[u8;1880]=kani::any();
  let index:usize=kani::any();
  kani::assume(index<144);
  if let Ok(statement)=decode(&original) {
   kani::cover!(matches!(statement,aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1::PrivateTransfer{..}));
   kani::cover!(matches!(statement,aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1::Withdrawal{..}));
   if let Ok(encoded)=encode(&statement) {
    assert_eq!(encoded[index],original[index]);
   }
  }
 }
}
''')
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'source-manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Exact frozen native complete decoder/encoder, no stubs or source changes; selected common/header byte equality on accepted decode and encode. Does not establish remaining bytes or Lean/native SDK installation.'),indent=2)+'\n')
print(O)
