#!/usr/bin/env python3
"""Exact Backend::c2 caller, actual owned carriers, explicit constructor boundaries."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
ROOT=Path(__file__).resolve().parents[5]
HOME=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
class Source:
 def __init__(self,b):self.b=b
 def read_bytes(self):return self.b

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--revision',required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 rev=subprocess.check_output(['git','-C',str(ROOT),'rev-parse',a.revision]).decode().strip()
 spec=importlib.util.spec_from_file_location('cut',ROOT/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 cuts=[];outputs={}
 def cut(name,path,anchor):
  raw=subprocess.check_output(['git','-C',str(ROOT),'show',rev+':'+path]);b,start,end,line,last=m.find_item(Source(raw),anchor)
  cuts.append(dict(name=name,path=path,source_file_sha256=sha(raw),start_byte=start,end_byte_exclusive=end,start_line=line,end_line_exclusive=last,sha256=sha(b)))
  outputs['fragments/'+name+'.rs']=b;return b.decode()
 core='crates/aspis-core/src/';host='crates/aspis-r1-cost-probe/src/'
 m31=cut('m31',core+'field.rs','#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]\npub struct M31(')
 cm31=cut('cm31',core+'field.rs','#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]\npub struct CM31 {')
 qm31=cut('qm31',core+'field.rs','#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]\npub struct QM31 {')
 qzero=cut('qm31_zero',core+'field.rs','pub const ZERO: QM31 = QM31 {')
 wide=cut('wide',core+'field/wide_exact.rs','#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]\npub struct WideExact {')
 embed=cut('wide_from_qm31',core+'field/wide_exact.rs','#[inline(always)]\n    pub fn from_qm31(')
 canon=cut('canonical_qm31',core+'field/wide_exact.rs','fn canonical_qm31(')
 p=cut('p',core+'field.rs','pub const P: u32 =')
 hashfn=cut('hashfn',core+'transcript.rs','pub type HashFn =')
 msg=cut('message_alias',core+'r0/mod.rs','pub type Message<E> =');msglen=cut('message_len',core+'r0/mod.rs','pub const MESSAGE_LEN: usize =')
 rerror=cut('r0_error',core+'r0/mod.rs','#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub enum Error {')
 serror=cut('semantic_error',host+'r1_wire.rs','#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub enum Error {')
 point=cut('point',core+'r0/domain.rs','#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub struct Point<E> {')
 tree=cut('tree',core+'r0/merkle.rs','pub struct Tree {');digest=cut('digest',core+'r0/merkle.rs','pub type Digest =')
 variant=cut('variant',host+'transport.rs','#[derive(Clone,Copy,Debug,PartialEq,Eq)]\npub enum Variant {')
 domain=cut('encoding_domain',host+'host_commitment.rs','pub struct EncodingDomain {')
 time=cut('commitment_time',host+'host_commitment.rs','#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub enum CommitmentTime {')
 word=cut('word',host+'host_commitment.rs','enum Word {');commitment=cut('commitment',host+'host_commitment.rs','pub struct Commitment {')
 salts=cut('private_salts',host+'host_commitment.rs','pub struct PrivateSalts(')
 new=cut('commitment_new',host+'host_commitment.rs','    pub fn new(\n        hash: HashFn,')
 salted=cut('commitment_new_salted',host+'host_commitment.rs','    pub fn new_salted(')
 root=cut('commitment_root',host+'host_commitment.rs','    pub fn root(&self)')
 backend=cut('backend',host+'prover.rs','pub struct Backend {')
 c2=cut('backend_c2',host+'prover.rs','    fn c2(&mut self,columns:')
 column=cut('column',host+'host_semantic.rs',"    #[derive(Clone, Copy)]\n    pub enum Column<'a>")
 trait=cut('commitments',host+'host_semantic.rs','    pub trait Commitments {')
 # The three nonsemantic boundary bodies MUST be opaque. They convey types
 # only. Omitting PrivateSalts::Drop is an explicit destruction/erasure boundary.
 lib='''#![no_std]
extern crate alloc;
extern crate self as aspis_core;
'''+hashfn+'''\npub mod field {\n'''+p+'\n'+m31+'\n'+cm31+'\n'+qm31+'''\nimpl QM31 {\n'''+qzero+'''\n}
pub mod wide_exact { use super::{M31,CM31,QM31,P};\n'''+wide+'\n'+canon+'\nimpl WideExact {\n'+embed+'''\n}}
pub use wide_exact::WideExact;
}
pub mod r0 {\n'''+msglen+'\n'+msg+'\n'+rerror+'''\npub mod domain {\n'''+point+'''\n}
pub mod merkle {use alloc::vec::Vec;\n'''+digest+'\n'+tree+'''\nimpl Tree {pub fn root(&self)->Digest {unreachable!()}} }
}
pub mod transport {\n'''+variant+'''\n}
pub mod r1_wire {\n'''+serror+'''\n}
pub mod host_semantic { use crate::{field::{M31,QM31},r1_wire::Error};\n'''+column+'\n'+trait+'''\n}
pub mod host_commitment {use alloc::vec::Vec; use crate::{HashFn,field::{WideExact as E,M31,QM31},r0::{domain::Point,merkle::Tree,Error,Message}};\n'''+domain+'\n'+time+'\n'+word+'\n'+commitment+'\n'+salts+'''\nimpl Commitment {\n'''+new+'\n'+salted+'\n'+root+'''
fn build(_:HashFn,_:&EncodingDomain,_:CommitmentTime,_:&[Message<E>],_:crate::transport::Variant,_:Option<PrivateSalts>)->Result<Self,Error>{unreachable!()}
}}
pub mod prover {use alloc::vec::Vec;use crate::{HashFn,field::{WideExact as E,QM31 as K},r0::Message,transport::Variant,host_commitment::{Commitment,CommitmentTime,EncodingDomain},host_semantic::{Column,Commitments},r1_wire::Error as SError};\n'''+backend+'''\nimpl Commitments for Backend {fn c1(&mut self,_:[Column<'_>;27])->Result<[u8;32],SError>{unreachable!()}\n'''+c2+'''\n}}
pub fn c2_entry(backend:&mut prover::Backend,columns:[&[field::QM31;1024];2])->Result<[u8;32],r1_wire::Error> {host_semantic::Commitments::c2(backend,columns)}
'''
 outputs['lib.rs']=lib.encode();outputs['Cargo.toml']=b'[package]\nname="aspis-c2-owned-host"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n[features]\nr0=[]\nprivate-leaf-salts=[]\n'
 outputs['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-c2-owned-host"\nversion = "0.0.0"\n'
 pins=dict(revision=rev,cuts=cuts,kit_files={n:sha(b) for n,b in outputs.items()},features=['r0','private-leaf-salts'],opaque_paths=['crate::host_commitment::_::build','crate::r0::merkle::_::root','crate::prover::_::c1'],root_target='crate::c2_entry',namespace='AspisC2OwnedHost',classification='Exact Backend::c2 caller and owned carriers; exact embedding/canonicalization; constructor/merkle-root/destruction boundaries explicit',boundaries={'constructor':'Commitment::build is a typechecking stub, must be an explicit universal parameter, never interpreted from its body/type. new/new_salted actual delegation bodies retained.','root':'Tree::root is a typechecking stub, explicit universal parameter; Commitment::root actual delegate retained.','c1':'Unused trait c1 implementation is a typechecking stub and excluded from C2 claim.','destruction':'PrivateSalts::Drop volatile erasure and implicit drops not modeled by this cut. No memory-erasure/custody theorem follows.','scope':'Caller functional state mutation/ownership first; coefficients/encode/word contents require actual build extraction, not this boundary.'})
 outputs['source-pins.json']=(json.dumps(pins,indent=2,sort_keys=True)+'\n').encode()
 for n,b in outputs.items():
  dest=a.out/n
  if a.check:assert dest.read_bytes()==b,n
  else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 print(json.dumps(dict(check=a.check,revision=rev,cuts=len(cuts),lib_sha256=sha(outputs['lib.rs']),pins_sha256=sha(outputs['source-pins.json']))))
if __name__=='__main__':main()
