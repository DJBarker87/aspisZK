from pathlib import Path
import json,hashlib,re,shutil
E=Path(__file__).resolve().parent; R=E.parents[4]; N=E/'RealR3_native';N.mkdir(exist_ok=True)
w=(R/'crates/aspis-r1-cost-probe/src/r1_wire.rs').read_text()
s=(R/'crates/aspis-r1-cost-probe/src/host_semantic.rs').read_text()
def item(src,needle):
 start=src.index(needle); begin=src.index('{',start);depth=1;i=begin+1
 while depth:
  if src[i]=='{':depth+=1
  elif src[i]=='}':depth-=1
  i+=1
 return src[start:i]
spans={name:item(w,needle) for name,needle in [
 ('error','pub enum Error'),('shape','pub const fn row_shape'),('fields','fn validate_record_fields'),('parse','pub fn parse_record'),('record','pub fn record'),
 ('sample_validated','fn sample_block_validated'),('sample','fn sample_block('),('semantic','pub fn semantic(&mut self'),('fields20','pub mod fields20'),('semantic20','pub mod semantic20')]}
# fields20/semantic20 have only local imports plus the same concrete field decoder.
closure=s[s.index('let framed = wire::record(row, payload)?;'):s.index('Ok::<QM31, Error>(value)')+len('Ok::<QM31, Error>(value)')]
assert closure.count('bytes.extend_from_slice(&framed)')==1
prefix='''#![allow(dead_code,unexpected_cfgs)]
extern crate alloc;
pub mod field;
pub mod aspis_core {pub use crate::field; pub trait Digest32 {fn digest(&self,parts:&[&[u8]])->[u8;32];}}
pub mod sampler {use crate::field::QM31; pub fn qm31_sample(block:&[u8;32])->QM31 {QM31::from_le_bytes(&block[..16]).unwrap_or(QM31::ZERO)}}
mod wire {
use alloc::vec::Vec;
use crate::field::{WideExact,QM31};
use crate::sampler::qm31_sample;
use crate::aspis_core::Digest32;
pub const CLAIMS:usize=87;pub const LANES:usize=29;
'''
# Rust2018 crate qualification only. No function body is rewritten.
spans={k:v.replace('use aspis_core::','use crate::aspis_core::') for k,v in spans.items()}
text=prefix+'#[derive(Clone,Copy,Debug,PartialEq,Eq)]\n'+spans['error']+'\n'
text+='\n'.join(spans[k] for k in ['shape','fields','parse','record'])
text+='''
#[derive(Clone)]
pub struct SemanticTranscript<H:Digest32>{pub state:[u8;32],pub hash:H,pub next_row:u8}
impl<H:Digest32> SemanticTranscript<H>{
'''+ '\n'.join(spans[k] for k in ['sample_validated','sample','semantic'])+'\n}\n'
text+='\n'.join(spans[k] for k in ['fields20','semantic20'])+'\n}\n'
text+='''
use crate::{field::QM31,wire::{Error,SemanticTranscript},aspis_core::Digest32};
fn native<H:Digest32>(row:u8,payload:&[u8],transcript:&mut SemanticTranscript<H>,bytes:&mut Vec<u8>)->Result<QM31,Error>{
'''+closure+'''\n}
fn owned<H:Digest32>(row:u8,payload:Vec<u8>,transcript:SemanticTranscript<H>,mut bytes:Vec<u8>)
 ->(Result<QM31,Error>,SemanticTranscript<H>,Vec<u8>){
 let framed=match wire::record(row,&payload){Ok(x)=>x,Err(e)=>return (Err(e),transcript,bytes)};
 let (out,next)=wire::semantic20::semantic(transcript,row,framed.clone());
 match out {Err(e)=>(Err(e),next,bytes),Ok(v)=>{bytes.extend_from_slice(&framed);(Ok(v),next,bytes)}}
}
'''
(N/'lib.rs').write_text(text+(E/'RealR3_scalar_harness.rs').read_text()+(E/'RealR3_context.rs').read_text()+(E/'RealR3_context_harness.rs').read_text())
(N/'Cargo.toml').write_text('[package]\nname="real-r3-native"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[features]\ndefault=["r1p-check"]\nr1p-check=[]\n[workspace]\n')
F=R/'docs/research/100bit-spend-path-20261013/evidence/prover-commit55-20261023/native'
shutil.copy2(F/'field.rs',N/'field.rs');shutil.copytree(F/'field',N/'field',dirs_exist_ok=True)
(E/'RealR3_native-bindings.json').write_text(json.dumps({'spans':{k:hashlib.sha256(v.encode()).hexdigest() for k,v in spans.items()},'closure':closure,'adjustment':'only use aspis_core -> use crate::aspis_core for standalone namespace; field library copied from part55','sampler_cut':'common pure sampler at equal challenge blocks; arbitrary four-word output is checked by Kani stub','native':'literal scalar closure with actual record/parser/semantic methods','owned':'semantic20 reference plus successful append'},indent=2)+'\n')
