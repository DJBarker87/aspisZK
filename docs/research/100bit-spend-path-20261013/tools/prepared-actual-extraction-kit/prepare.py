#!/usr/bin/env python3
"""Whole actual caller bodies over canonical52cut carriers and explicit boundaries."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
R=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent
REV='3335eecf2f2a08096abe95c67ac6b304f2df6284'
BASE_REV='c16ab4d76619cf2cf80ece9d7e60e47975957af0'
sha=lambda b:hashlib.sha256(b).hexdigest()
class Source:
 def __init__(self,b):self.b=b
 def read_bytes(self):return self.b

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--base-kit',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 spec=importlib.util.spec_from_file_location('cut',R/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 basepins=json.loads((a.base_kit/'source-pins.json').read_text());base=(a.base_kit/'lib.rs').read_bytes();assert len(basepins['cuts'])==52 and basepins['revision']==BASE_REV
 assert sha(base)==basepins['kit_files']['lib.rs']
 outputs={'base52/lib.rs':base,'base52/source-pins.json':(a.base_kit/'source-pins.json').read_bytes()};cuts=[]
 def cut(name,path,anchor):
  raw=subprocess.check_output(['git','-C',str(R),'show',REV+':'+path]);b,start,end,line,last=m.find_item(Source(raw),anchor)
  cuts.append(dict(name=name,path=path,source_file_sha256=sha(raw),start_byte=start,end_byte_exclusive=end,start_line=line,end_line_exclusive=last,sha256=sha(b)));outputs['fragments/'+name+'.rs']=b
  return b.decode()
 sem='crates/aspis-r1-cost-probe/src/r1_semantic.rs';ver='crates/aspis-r1-cost-probe/src/verifier.rs';wire='crates/aspis-r1-cost-probe/src/r1_wire.rs';trans='crates/aspis-r1-cost-probe/src/transcript.rs'
 verified=cut('verified',sem,'pub struct Verified<H: Digest32>');verify=cut('verify_observed',sem,'#[inline(never)]\npub fn verify_observed<H: Digest32>')
 claim=cut('prepared_claim',ver,'fn prepared_claim<H:Digest32>')
 prepared=cut('prepared',ver,'pub struct Prepared {');prepare=cut('prepared_new',ver,'#[inline(never)]\n    pub fn new<H:Digest32>');view=cut('view',ver,"pub struct View<'a>")
 phase=cut('phase',ver,'#[derive(Debug,Clone,Copy,PartialEq,Eq)]\npub enum Phase');error=cut('verifier_error',ver,'#[derive(Debug,Clone,Copy,PartialEq,Eq)]\npub enum Error')
 point=cut('secure_circle_point','crates/aspis-core/src/circle.rs','#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub struct SecureCirclePoint')
 wide=cut('wide_exact','crates/aspis-core/src/field/wide_exact.rs','#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]\npub struct WideExact')
 widezero=cut('wide_zero','crates/aspis-core/src/field/wide_exact.rs','pub const ZERO: Self = Self {')
 state=cut('semantic_state',wire,'pub fn state(&self)');payload=cut('prefix_payload',wire,'pub fn payload(&self, row: u8)');circle=cut('circle_validated',wire,'pub(crate) fn circle_validated(')
 circlerow=cut('circle_row','crates/aspis-core/src/r0_transcript.rs','#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub enum CircleRow')
 folds=cut('variant_folds','crates/aspis-r1-cost-probe/src/transport.rs','pub fn folds(self)')
 scalar=cut('opening_scalar',trans,'pub fn scalar(&mut self,');scalar_k=cut('opening_scalar_k',trans,'pub fn scalar_k(&mut self,')
 dot=cut('dot_type','crates/aspis-r1-cost-probe/src/fast_pairing.rs','pub struct Dot {');eby=cut('eby_type','crates/aspis-r1-cost-probe/src/fast_pairing.rs','pub struct EbyKDot {')
 trace=cut('trace_value','crates/aspis-r1-cost-probe/src/trace.rs','pub fn value(tag: u16,')
 # A boundary stub is never a theorem interpretation. Charon must classify
 # every listed function opaque; the final Lean model must replace it with an
 # explicit argument or checked actual model. Caller bodies above are exact.
 lib=base.decode()
 lib=lib.replace('pub mod aspis_core {','pub mod aspis_core {\n pub mod circle { use super::field::QM31;\n'+point+'\n}\n pub mod state_only_hiding { use super::field::QM31; pub fn state_only_selected_mask_value(_: &[QM31;16],_: &[QM31;10],_:QM31,_:&[QM31;10])->QM31 {unreachable!()} }',1)
 lib=lib.replace('    pub mod field {','    pub mod field {\n'+wide+'\n impl WideExact {\n'+widezero+'\n pub fn to_le_bytes(self)->[u8;32]{unreachable!()} pub fn c0(self)->QM31 {self.c0} pub fn from_qm31(_:QM31)->Self {unreachable!()} pub fn from_m31(_:M31)->Self {unreachable!()} pub fn add(self,_:Self)->Self {unreachable!()} pub fn mul(self,_:Self)->Self {unreachable!()} }\n impl QM31 { pub fn add(self,_:Self)->Self {unreachable!()} pub fn mul(self,_:Self)->Self {unreachable!()} }',1)
 lib=lib.replace('        pub mod r0 {','        pub mod r0 {\n pub use crate::r1_wire::Challenges;',1)
 lib=lib.replace("            impl<'a> Public<'a> {", "            impl<'a> Public<'a> {\n pub fn terminal_qm31(self,_:&[[crate::aspis_core::field::QM31;29];3],_:&[crate::aspis_core::field::QM31;10],_:&crate::r1_wire::Challenges)->Result<crate::aspis_core::field::QM31,Error> {unreachable!()}",1)
 lib=lib.replace('pub mod sampler {','pub mod sampler {\n use crate::aspis_core::{circle::SecureCirclePoint,field::WideExact};\n'+circlerow+'\n pub fn circle_sample(_:&[u8;32],_:CircleRow)->SecureCirclePoint {unreachable!()} pub fn ordinary_sample(_:&[u8;32])->WideExact {unreachable!()} pub fn gamma_sample(_:&[u8;32])->WideExact {unreachable!()}',1)
 lib=lib.replace('pub mod r1_wire {','pub mod r1_wire {\n use crate::aspis_core::circle::SecureCirclePoint; use crate::sampler::{circle_sample,CircleRow};',1)
 lib=lib.replace(" impl<'a> ValidatedRecord<'a> {", " impl<'a> ValidatedRecord<'a> {\n pub(crate) fn decode_k<const N:usize>(&self,_:usize)->Result<[QM31;N],Error>{unreachable!()}",1)
 lib=lib.replace(" impl<'a> Prefix<'a> {", " impl<'a> Prefix<'a> {\n pub fn parse(_:&'a[u8])->Result<Self,Error>{unreachable!()}\n"+payload,1)
 lib=lib.replace('    impl<H: Digest32> SemanticTranscript<H> {','    impl<H: Digest32> SemanticTranscript<H> {\n'+state+'\n'+circle,1)
 lib=lib.replace('pub mod r1_semantic {','pub mod r1_semantic {\n use crate::aspis_core; use crate::r1_wire as wire; use alloc::boxed::Box; use crate::r1_wire::{Prefix,Challenges}; use crate::aspis_core::{circle::SecureCirclePoint,field::QM31};\n'+verified+'\n fn claims(_:&Prefix)->Result<Box<[[QM31;29];3]>,Error>{unreachable!()}\n'+verify,1)
 lib=lib.replace(' impl Variant {',' impl Variant {\n'+folds,1)
 lib=lib.replace('pub mod transcript {','pub mod transcript {\n use crate::aspis_core; use crate::aspis_core::field::WideExact as E;',1)
 lib=lib.replace(' impl<H: Digest32> Transcript<H> {',' impl<H: Digest32> Transcript<H> {\n'+scalar+'\n'+scalar_k+'\n pub fn queries(&mut self,_:u8,_:&[u8])->Result<[u32;22],crate::verifier::Error> {unreachable!()}',1)
 lib+='''\npub mod trace {use crate::aspis_core::field::WideExact as E;\n'''+trace+'''\n}
pub mod weights {use crate::aspis_core::field::WideExact as E; pub fn powers<const N:usize>(_:E)->[E;N] {unreachable!()} pub fn field(_:&[u8],_:usize)->E {unreachable!()} }
pub mod fast_pairing {use crate::aspis_core::field::{WideExact as E,QM31}; mod canonical {'''+dot+'''} '''+eby+''' impl EbyKDot {pub fn new()->Self {unreachable!()} pub fn push(&mut self,_:E,_:QM31)->Result<(),()>{unreachable!()} pub fn finish(self)->E {unreachable!()} } }
pub mod verifier {use alloc::{boxed::Box,vec::Vec}; use crate::{aspis_core::{Digest32,field::{WideExact as E,QM31 as K},circle::SecureCirclePoint},transport::Variant,transcript::Transcript,weights::{powers,field}};\n'''+error+'\n'+phase+'''\npub type Observer=Option<fn(Phase)>;\n'''+view+'\n'+prepared+'\n'+claim+'\n impl Prepared {\n'+prepare+'''\n} }
pub fn prepared_entry<H:crate::aspis_core::Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&crate::verifier::View<'_>,hash:H)->Result<alloc::boxed::Box<crate::verifier::Prepared>,crate::verifier::Error>{crate::verifier::Prepared::new(sem,v,hash)}
'''
 outputs['lib.rs']=lib.encode();outputs['Cargo.toml']=b'[package]\nname="aspis-r1-verify-prepared-prefix"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n[features]\nr0=[]\nprivate-leaf-salts=[]\ndetail-phases=[]\nprover=[]\n'
 outputs['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-r1-verify-prepared-prefix"\nversion = "0.0.0"\n'
 opaque=['crate::r1_wire::_::parse','crate::r1_wire::_::decode_k','crate::r1_semantic::claims','crate::pool_v1::pair_forest_semantic_terminal::r0::_::terminal_qm31','crate::aspis_core::state_only_hiding','crate::aspis_core::field::_::add','crate::aspis_core::field::_::mul','crate::aspis_core::field::_::from_qm31','crate::aspis_core::field::_::from_m31','crate::aspis_core::field::_::to_le_bytes','crate::sampler::circle_sample','crate::sampler::ordinary_sample','crate::sampler::gamma_sample','crate::transcript::_::queries','crate::weights','crate::fast_pairing','crate::verifier::prepared_claim']
 pins={'revision':REV,'base52_lib_sha256':sha(base),'base52_cuts':basepins['cuts'],'cuts':cuts,'opaque_paths':opaque,'features':['r0','private-leaf-salts'],'kit_files':{n:sha(b) for n,b in outputs.items()},'scope':'Exact accepted3335 Prepared::new/prepared_claim and unchanged verify_observed/schedule helper cuts over canonical52-cut carriers. Preparedroot only emitted; verify not claimed. Boundary bodies are explicit nonsemantic typechecking stubs, must be opaque and replaced by explicit universal parameters or checked definitions. No theorem may use stub behavior or a global opaque axiom.'}
 outputs['source-pins.json']=(json.dumps(pins,indent=2,sort_keys=True)+'\n').encode()
 for n,b in outputs.items():
  p=a.out/n
  if a.check:assert p.read_bytes()==b,n
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 print(json.dumps({'check':a.check,'exact_cuts':len(cuts),'lib_sha256':sha(outputs['lib.rs']),'lines':lib.count('\n'),'opaque_boundaries':len(opaque)}))
if __name__=='__main__':main()
