#!/usr/bin/env python3
"""Full owned SDK byte-step/count reference; no production source adoption.
The loop must be proved equal to the existing full owned final assignment,
then joined to the checked native byte-step and frozen whole-copy boundary.
"""
from pathlib import Path
import sys,json,hashlib
O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
s='''use aspis_s126_owned_sdk::OwnedSdk;
use solana_program::program_error::ProgramError;

pub fn copy_step(sdk:&mut OwnedSdk,slot:usize,source:&[u8],offset:usize) {
 sdk.data_cells[slot].bytes[offset]=source[offset];
}

pub fn copy_in_place(sdk:&mut OwnedSdk,slot:usize,source:&[u8])->Result<(),ProgramError> {
 if sdk.data_cells[slot].bytes.len()!=source.len() {
  return Err(ProgramError::InvalidAccountData);
 }
 let mut offset=0;
 while offset<source.len() {
  copy_step(sdk,slot,source,offset);
  offset+=1;
 }
 Ok(())
}
'''
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-owned-sdk-copy"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
aspis-s126-owned-sdk={path="/home/dombarker/project-offloads/s126-real-sdk-20261021/owned-sdk-v3"}
[profile.release]
opt-level=3
overflow-checks=true
''')
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',protocol_freeze='b2727acd3abf79315d18b754a260f58f4b1c6326',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,types='Actual full OwnedSdk from the pinned owned-sdk-v3 dependency: accounts, data and lamport cells, every key/owner/flag/rent/counter/Rc field. No new carrier or IO callbacks.',remaining='Extraction/type identity checks, exact step/update semantics, count induction with integer/index totality, equality to the original full owned final assignment, native whole-copy and caller transport. No adoption/re-pin of frozen production is implied.'),indent=2)+'\n')
