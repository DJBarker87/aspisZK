#!/usr/bin/env python3
"""Owned buffer reference for the frozen stage1 continuation, extraction-only.

The live SDK wrapper must retain guards and acquire public/proof snapshots at
their original program points. The two snapshot operations remain named IO
children, not pre-evaluated/reordered inputs or an asserted SDK refinement.
"""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
rev='b2727acd3abf79315d18b754a260f58f4b1c6326'
def frozen(p):return subprocess.check_output(['git','-C',str(R),'show',rev+':'+p],text=True)
adapter=frozen('programs/r1-cost-probe/src/r1_pool_adapter.rs');program=frozen('programs/r1-cost-probe/src/lib.rs')
def cut(s,n):
 a=s.index('fn '+n);i=s.index('{',a)+1;d=1
 while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
stage=cut(adapter,'stage1');suffix=stage[stage.index('    let public_data ='):]
suffix=suffix.replace('public_account.try_borrow_data()?','read_public_snapshot()?').replace('proof_account.try_borrow_data()?','read_proof_snapshot()?').replace('super::first_decoded','first_decoded')
s='''#![allow(dead_code,unexpected_cfgs)]
use aspis_r1_cost_probe::{verifier,transport::Variant};
use aspis_statement::pool_v1::{PoolV1PairForestTerminalStatementV1,POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,decode_pool_v1_pair_forest_terminal_statement_v1,validate_pool_v1_pair_forest_terminal_statement_v1,encode_pool_v1_pair_verified_afterstate_v1};
use solana_program::{program_error::ProgramError,entrypoint::ProgramResult,hash::hashv,msg};
#[derive(Clone,Copy)] struct SolanaDigest;
impl aspis_core::Digest32 for SolanaDigest {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {hashv(parts).to_bytes()}
}
// The exact cfg-off observer body. Error logging remains a distinct child.
fn observer()->verifier::Observer {None}
'''+cut(program,'error')+'\n'+cut(program,'first_decoded')+'\n'+cut(adapter,'decode_public_statement_box')+'''
// Ordered SDK IO child signatures. Their implementations are supplied by the
// live guard-retaining wrapper; these panic bodies are never translated.
fn read_public_snapshot()->Result<Vec<u8>,ProgramError>{panic!("SDK IO boundary")}
fn read_proof_snapshot()->Result<Vec<u8>,ProgramError>{panic!("SDK IO boundary")}
pub fn owned_stage1_tail(checkpoint_data:&mut [u8], data:&[u8])->ProgramResult {
'''+suffix+'''
// Owned zero-scan reference. SDK/standard-iterator correspondence is a
// separate base/step/exit certificate, never inferred just from extraction.
pub fn owned_checkpoint_nonzero(bytes:Vec<u8>)->bool {
 let mut i=0;
 while i<bytes.len() {
  if bytes[i]!=0 {return true;}
  i+=1;
 }
 false
}
'''
(O/'src/lib.rs').write_text(s)
host='/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src'
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-owned-stage1"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
aspis-core={path="ROOT/crates/aspis-core",features=["r0"]}
aspis-statement={path="ROOT/crates/aspis-statement",features=["r0","pool-v1-kernel"]}
aspis-r1-cost-probe={path="ROOT/crates/aspis-r1-cost-probe",features=["optimized-terminal","program-build"]}
[profile.release]
opt-level=3
overflow-checks=true
'''.replace('ROOT',host))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=rev,source_sha256=hashlib.sha256(s.encode()).hexdigest(),original_suffix=stage[stage.index('    let public_data ='):],changes=['SDK public/proof Ref guards replaced by ordered named owned-snapshot IO children','checkpoint is an owned-reference mutable slice','super path resolved locally','release observer exact cfg-off body'],qualification='Extraction candidate only. Not a claim that IO children have been supplied or SDK-to-reference equivalence proved. Keeps exact error and full statement/verifier carriers and actual semantic_public/common methods. Snapshot children must execute at the original points while guards remain live.'),indent=2)+'\n')
