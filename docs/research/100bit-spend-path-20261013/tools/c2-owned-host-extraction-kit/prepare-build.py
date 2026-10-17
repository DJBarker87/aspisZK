#!/usr/bin/env python3
"""Whole actual Commitment::build over explicit encoder/hash/allocation boundaries.
The body is never specialized, stubbed, or inferred from a result type.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
ROOT=Path(__file__).resolve().parents[5]
sha=lambda b:hashlib.sha256(b).hexdigest()
class Source:
 def __init__(self,b):self.b=b
 def read_bytes(self):return self.b

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--base-kit',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 base=a.base_kit;pins=json.loads((base/'source-pins.json').read_text());rev=pins['revision'];lib=(base/'lib.rs').read_text();assert sha(lib.encode())==pins['kit_files']['lib.rs']
 spec=importlib.util.spec_from_file_location('cut',ROOT/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 outputs={};cuts=[]
 def cut(name,path,anchor):
  raw=subprocess.check_output(['git','-C',str(ROOT),'show',rev+':'+path]);b,start,end,line,last=m.find_item(Source(raw),anchor)
  cuts.append(dict(name=name,path=path,source_file_sha256=sha(raw),start_byte=start,end_byte_exclusive=end,start_line=line,end_line_exclusive=last,sha256=sha(b)));outputs['fragments/'+name+'.rs']=b;return b.decode()
 c='crates/aspis-core/src/';h='crates/aspis-r1-cost-probe/src/'
 build=cut('commitment_build',h+'host_commitment.rs','    fn build(')
 saltsget=cut('salts_get',h+'host_commitment.rs','    pub fn get(&self, index:');saltslen=cut('salts_len',h+'host_commitment.rs','    fn len(&self)')
 c0=cut('wide_c0',c+'field/wide_exact.rs','#[inline(always)]\n    pub const fn c0(')
 limbs=cut('wide_limbs',c+'field/wide_exact.rs','#[inline(always)]\n    pub const fn to_limbs(')
 lcount=cut('limb_count',c+'field/wide_exact.rs','pub const LIMB_COUNT: usize =')
 coef=cut('variant_coefficients',h+'transport.rs','    pub fn coefficients<');row=cut('variant_row',h+'transport.rs','    pub fn row(self,');tau=cut('tau',h+'transport.rs','pub const TAU:')
 coefftorow=cut('coefficient_to_row',c+'r0/transport.rs','pub const COEFFICIENT_TO_ROW:')
 order=cut('transport_order',c+'r0/transport.rs','const fn order(')
 pads=cut('pad_rows',c+'r0/transport_pads.rs','pub const PAD_ROWS:');npads=cut('pads_count',c+'r0/transport.rs','pub const PADS:');pivot=cut('pivot',c+'r0/transport.rs','pub const PIVOT:')
 fibres=cut('fibre_count',c+'r0/mod.rs','pub const FIBRE_COUNT:');lanes=cut('lanes',c+'r0/opening.rs','pub const LANES:')
 c1tag=cut('c1_tag',c+'r0/merkle.rs','pub const C1_TAG:');c2tag=cut('c2_tag',c+'r0/merkle.rs','pub const C2_TAG:')
 # Encoder boundary keeps the actual generic function's Copy requirement but
 # intentionally omits CodeField dictionary: its body is opaque, and the
 # owned-vector theorem quantifies over its M31/QM31 results. No arithmetic law
 # or encoder result is inferred from that signature weakening.
 lib=lib.replace('impl WideExact {\n','impl WideExact {\n'+lcount+'\n'+c0+'\n'+limbs+'\n',1)
 lib=lib.replace('pub mod r0 {\n','pub mod r0 {\n'+fibres+'\n pub mod opening {\n'+lanes+'\n}\npub mod heap { use alloc::vec::Vec; use super::Error; pub fn filled<T:Copy>(_:usize,_:T)->Result<Vec<T>,Error>{unreachable!()} }\npub mod transport {use super::MESSAGE_LEN;\n'+pads+'\n'+npads+'\n'+pivot+'\n'+coefftorow+'\n'+order+'\n}\n',1)
 lib=lib.replace('impl Tree {pub fn root','impl Tree {pub fn new(_:crate::HashFn,_:Vec<Digest>)->Result<Self,super::Error>{unreachable!()} pub fn root',1)
 lib=lib.replace('pub mod merkle {use alloc::vec::Vec;','pub mod merkle {use alloc::vec::Vec;\n'+c1tag+'\n'+c2tag+'\npub fn leaf(_:crate::HashFn,_:u8,_:&[u8])->Digest {unreachable!()}\n',1)
 lib=lib.replace('pub mod transport {\n'+(base/'fragments/variant.rs').read_text(),'pub mod transport {\n'+(base/'fragments/variant.rs').read_text()+'\n'+tau+'\nimpl Variant {\n'+row+'\n'+coef+'\n}',1)
 lib=lib.replace('pub mod host_commitment {use alloc::vec::Vec;', 'pub mod state_only_private_merkle {pub fn private_leaf_hash(_:crate::HashFn,_:u8,_:&[u8],_:&[u8;32])->[u8;32]{unreachable!()}}\npub mod host_commitment {use crate::r0::{heap::filled,opening::LANES,FIBRE_COUNT,merkle};use alloc::vec::Vec;',1)
 lib=lib.replace('impl Commitment {\n','impl EncodingDomain {pub fn encode<T:Copy>(&self,_:&Message<T>)->Result<Vec<T>,Error>{unreachable!()}}\nimpl PrivateSalts {\n'+saltsget+'\n'+saltslen+'\n}\nimpl Word {fn value(&self,_:usize)->E {unreachable!()}}\nimpl E {pub fn to_le_bytes(self)->[u8;32]{unreachable!()}}\nimpl Commitment {\n',1)
 old='fn build(_:HashFn,_:&EncodingDomain,_:CommitmentTime,_:&[Message<E>],_:crate::transport::Variant,_:Option<PrivateSalts>)->Result<Self,Error>{unreachable!()}'
 assert lib.count(old)==1;lib=lib.replace(old,build)
 lib=lib.replace('\n}}\npub mod prover {','\n}\npub fn c2_build_entry(hash:HashFn,domain:&EncodingDomain,messages:&[Message<E>],variant:crate::transport::Variant,salts:Option<PrivateSalts>)->Result<Commitment,Error>{Commitment::build(hash,domain,CommitmentTime::C2,messages,variant,salts)}\n}\npub mod prover {',1)
 outputs['lib.rs']=lib.encode()
 for n in ['Cargo.toml','Cargo.lock']:outputs[n]=(base/n).read_bytes()
 newpins=dict(revision=rev,base_caller_cuts=pins['cuts'],cuts=cuts,kit_files={n:sha(b) for n,b in outputs.items()},features=pins['features'],root_target='crate::host_commitment::c2_build_entry',namespace='AspisC2OwnedBuild',opaque_paths=['crate::host_commitment::_::encode','crate::host_commitment::_::value','crate::host_commitment::_::to_le_bytes','crate::r0::heap::filled','crate::r0::merkle::_::new','crate::r0::merkle::_::root','crate::r0::merkle::leaf','crate::state_only_private_merkle::private_leaf_hash'],classification='Whole actual Commitment::build and variant coefficient transport, exact retained owned carriers; explicit allocation/encoder/packing/hash/tree boundaries',boundaries={**pins['boundaries'],'constructor':'Commitment::build actual entire body retained. Exact loops/errors/constructors, no source specialization.','encoder_signature':'Opaque encode<T:CodeField> boundary is represented by encode<T:Copy>; no CodeField instances/laws/results inferred. Only M31 and QM31 instantiations occur in build. Bind each actual encoder execution result explicitly.','packing_hash_tree':'Word::value, E::to_le_bytes, leaf hash and Tree::new are opaque. No packing/salt-path/collision or root claim.','filled':'Allocation helper opaque; exact length/content requires primitive filled specification, separate from desired owned-word conclusion.'})
 outputs['source-pins.json']=(json.dumps(newpins,indent=2,sort_keys=True)+'\n').encode()
 for n,b in outputs.items():
  dest=a.out/n
  if a.check:assert dest.read_bytes()==b,n
  else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 print(json.dumps(dict(check=a.check,revision=rev,body_cuts=len(cuts),lib_sha256=sha(lib.encode()),pins_sha256=sha(outputs['source-pins.json']))))
if __name__=='__main__':main()
