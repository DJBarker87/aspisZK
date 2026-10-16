#!/usr/bin/env python3
"""Exact first-body reachability extraction preflight, with explicit cut boundaries.
No stub semantics may be used in a theorem; this is a tool-support diagnostic.
"""
from pathlib import Path
import argparse, hashlib, importlib.util,json,subprocess
R=Path(__file__).resolve().parents[5]
H=Path(__file__).resolve().parent
REV='ebe378259fb7d9c8a007eec2c8a8eb4850e549fc'
sha=lambda x:hashlib.sha256(x).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 parser=R/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py'
 spec=importlib.util.spec_from_file_location('cut',parser);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 source=R/'programs/r1-cost-probe/src/lib.rs';first,start,end,line,last=m.find_item(source,'#[inline(never)]\nfn first(')
 assert source.read_bytes()[start:end]==first
 prep=(R/'docs/research/100bit-spend-path-20261013/tools/public-preparation-extraction-kit/lib.rs').read_text()
 # Only the exact existing carrier/selector declarations are needed. All opaque
 # boundaries are called out below and are not represented as proved semantics.
 phase='#[derive(Debug,Clone,Copy,PartialEq,Eq)]\npub enum Phase { Parsed,Semantic,SemanticPart(u8),Prepare,CheckpointRead,Merkle(usize),Query(usize),QueryPart(usize,u8),CheckpointWrite,Relation,Final }'
 verifier=R/'crates/aspis-r1-cost-probe/src/verifier.rs'
 vtext=verifier.read_text();assert phase in vtext
 lib=prep+'''\nuse alloc::vec::Vec;
use pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1;
use pool_v1::pair_forest_semantic_terminal::r0::Public;
#[derive(Clone, Copy)]
struct SolanaDigest;
#[derive(Clone, Copy)]
struct DecodeError;
#[derive(Clone, Copy)]
enum ProgramError { InvalidAccountData, InvalidInstructionData }
fn decode_pool_v1_pair_forest_terminal_statement_v1(_: &[u8]) -> Result<PoolV1PairForestTerminalStatementV1, DecodeError> { unreachable!() }
mod verifier {
use super::*;
'''+phase+'''
pub type Observer = Option<fn(Phase)>;
#[derive(Clone, Copy)]
pub struct Error;
pub fn tx1(public: Public<'_>, public_bytes: &[u8], proof: &[u8], k: usize, hash: SolanaDigest, obs: Observer) -> Result<Vec<u8>, Error> { unreachable!() }
}
fn mark(_: verifier::Phase) { unreachable!() }
fn error(_: verifier::Error) -> ProgramError { unreachable!() }
'''+first.decode()+'\n'
 files={'lib.rs':lib.encode(),'Cargo.toml':b'[package]\nname="aspis-r1-first-diagnostic"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n[features]\nr0=[]\nprivate-leaf-salts=[]\n',
 'Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-r1-first-diagnostic"\nversion = "0.0.0"\n'}
 pins={'revision':REV,'source':str(source.relative_to(R)),'source_file_sha256':sha(source.read_bytes()),'first':{'start_byte':start,'end_byte_exclusive':end,'start_line':line,'end_line_exclusive':last,'sha256':sha(first)},'kit_files':{n:sha(b) for n,b in files.items()},'features':['r0','private-leaf-salts'],
 'boundaries':'Diagnostic only. Decoder/tx1/mark/error are opaque. Decoder error, ProgramError and tx1 signature are stub carriers solely to isolate the exact production first body and its actual Observer function-pointer obstruction. These stubs cannot support an actual-first theorem.',
 'opaque_paths':['crate::decode_pool_v1_pair_forest_terminal_statement_v1','crate::verifier::tx1','crate::mark','crate::error']}
 files['source-pins.json']=(json.dumps(pins,indent=2,sort_keys=True)+'\n').encode()
 for n,b in files.items():
  p=a.out/n
  if a.check:assert p.read_bytes()==b,n
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 print(json.dumps({'check':a.check,'exact_first_sha256':sha(first),'lines':lib.count('\n'),'scope':'tool diagnostic only'}))
if __name__=='__main__':main()
