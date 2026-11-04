"""OPEN caller-G candidate: local records and one source-shaped iteration.

This is not a bridge claim for finish_query_dot. The real typed EbyKDot carrier
association from the copied source step, canonical NFG model substitution and loop/finalization join remain
OPEN. No field multiplication is executed or stubbed here.
"""
from pathlib import Path
import json,subprocess,hashlib
from NFU_add_inputs import update
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';I=json.loads((E/'NFU_NATIVE_INPUTS.json').read_text())
source=subprocess.check_output(['git','show','4bb3b3f:'+C+'verifier.rs'],text=True)
signature='fn finish_query_dot(final_message:&[u8],weights:&[K])->Result<E,Error> {'
lo=source.index(signature);hi=source.index('\n}',lo)+2;body=source[lo:hi]
code='''// OPEN one-iteration oracle candidate; no claimed actual Dot ABI transport.
use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log{reply:bool,after:[u64;9],before:[u64;9],value:[u32;8],scalar:[u32;4],calls:usize,order:u8,field_ptr:*const u8,field_len:usize,field_index:usize,weight_ptr:*const K,weight_index:usize}
fn recorded_push(dot:&mut crate::fast_pairing::EbyKDot,value:E,scalar:K,log:&mut Log)->Result<(),()>{log.before=crate::fast_pairing::NFU_helpers::read(dot);log.value=value.to_limbs();log.scalar=[scalar.c0.a.0,scalar.c0.b.0,scalar.c1.a.0,scalar.c1.b.0];log.calls+=1;log.order=if log.order==2{3}else{255};*dot=crate::fast_pairing::NFU_helpers::make(log.after);if log.reply{Ok(())}else{Err(())}}
fn recorded_field(bytes:&[u8],j:usize,log:&mut Log)->E{let selected=&bytes[32*j..32*(j+1)];log.field_ptr=selected.as_ptr();log.field_len=selected.len();log.field_index=j;log.order=1;field(bytes,j)}
fn recorded_weight(weights:&[K],j:usize,log:&mut Log)->K{log.weight_ptr=&weights[j];log.weight_index=j;log.order=if log.order==1{2}else{255};weights[j]}
fn source_step(final_message:&[u8],weights:&[K],dot:&mut crate::fast_pairing::EbyKDot,j:&mut usize,log:&mut Log)->Result<(),Error>{
 let value=recorded_field(final_message,*j,log);
 let scalar=recorded_weight(weights,*j,log);
 recorded_push(dot,value,scalar,log).map_err(|_|Error::Parse)?;*j+=1;Ok(())
}
fn exercise(group:u8){
 let mut bytes:[u8;2048]=kani::any();let j:usize=kani::any();kani::assume(j<64);
 let value:[u32;8]=kani::any();for x in value{kani::assume(x<0x7fffffff);}
 for i in 0..8{bytes[32*j+4*i..32*j+4*i+4].copy_from_slice(&value[i].to_le_bytes());}
 let scalar:[u32;4]=kani::any();let mut weights=[K::ZERO;64];weights[j]=K{c0:aspis_core::field::CM31{a:M31(scalar[0]),b:M31(scalar[1])},c1:aspis_core::field::CM31{a:M31(scalar[2]),b:M31(scalar[3])}};
 let before:[u64;9]=kani::any();let after:[u64;9]=kani::any();let reply:bool=kani::any();
 let mut log=Log{reply,after,before:[0;9],value:[0;8],scalar:[0;4],calls:0,order:0,field_ptr:core::ptr::null(),field_len:0,field_index:0,weight_ptr:core::ptr::null(),weight_index:0};
 let mut dot=crate::fast_pairing::NFU_helpers::make(before);let mut index=j;let result=source_step(&bytes,&weights,&mut dot,&mut index,&mut log);let final_state=crate::fast_pairing::NFU_helpers::read(&dot);
 let good=match group{
 0=>if reply{matches!(result,Ok(()))}else{matches!(result,Err(Error::Parse))},
 1=>index==if reply{j+1}else{j},2=>log.calls==1,3=>log.before==before,4=>final_state==after,
 5=>log.value[..4]==value[..4],6=>log.value[4..]==value[4..],7=>log.scalar==scalar,
 8=>log.value.iter().all(|x|*x<0x7fffffff),9=>log.order==3,
 10=>log.field_ptr==bytes.as_ptr().wrapping_add(32*j),11=>log.field_len==32,
 12=>log.field_index==j,13=>log.weight_ptr==weights.as_ptr().wrapping_add(j)&&log.weight_index==j,
 _=>false};assert!(good != cfg!(NFU_invert));
}
macro_rules! gate{($name:ident,$n:expr)=>{#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $name(){exercise($n)}};}
'''
for i in range(14):code+=f'gate!(finish_g{i:02},{i});\n'
fast=subprocess.check_output(['git','show','4bb3b3f:'+C+'fast_pairing.rs'],text=True)
fast=fast.replace('mod canonical {','mod canonical {\n #[cfg(kani)] pub(super) mod NFU_canonical { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/NFU_canonical.rs")); }',1)
fast+='\n#[cfg(kani)] #[path="NFU_fast_helpers.rs"] pub(crate) mod NFU_helpers;\n'
canonical="""use super::Dot;
pub(in crate::fast_pairing) fn read(dot:&Dot)->[u64;4]{dot.sums}
pub(in crate::fast_pairing) fn make(sums:[u64;4])->Dot{Dot{sums}}
"""
helpers="""use super::*;
pub(crate) fn read(dot:&EbyKDot)->[u64;9]{let a=canonical::NFU_canonical::read(&dot.c0);let b=canonical::NFU_canonical::read(&dot.c1);[a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3],dot.count as u64]}
pub(crate) fn make(s:[u64;9])->EbyKDot{assert_eq!(usize::BITS,64);EbyKDot{c0:canonical::NFU_canonical::make([s[0],s[1],s[2],s[3]]),c1:canonical::NFU_canonical::make([s[4],s[5],s[6],s[7]]),count:s[8] as usize}}
"""
update({C+'verifier.rs':source+'\n#[cfg(kani)]\n#[path="NFU_verifier.rs"]\nmod NFU_verifier;\n',C+'NFU_verifier.rs':code,C+'fast_pairing.rs':fast,C+'NFU_canonical.rs':canonical,C+'NFU_fast_helpers.rs':helpers},'NFU_finish_candidate')
(E/'NFU_FINISH_CANDIDATE.json').write_text(json.dumps(dict(status='OPEN; native caller-G candidate only',frozen_function='crates/aspis-r1-cost-probe/src/verifier.rs::finish_query_dot',frozen_source_sha256=hashlib.sha256(source.encode()).hexdigest(),frozen_body=body,frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),callee_domain='NFG public push: canonical E input, arbitrary raw scalar/count and old fields, valid unique receiver; source E decoder receives a SAME canonical32-byte window; no field products here',callee_provenance='evidence/slice-q-mul9-20261104/NFM_peer_inputs/NFG_CERTIFICATES.json',candidate_changes='One iteration only; local-record oracle on the ACTUAL typed EbyKDot replaces the push call, with full unconstrained reply and nine-word mutation. recorded_field/recorded_weight are ghost capture around the actual field/read. Typed field-by-field make/read helpers preserve the actual frozen struct; copied-step/source-loop and canonical model association remain OPEN.',remaining=['actual typed Dot/source-erasure/ABI association','canonical NFG model transport without old FIo imports','full finite-loop induction/new/finish/abort-prefix composition','caller domain and final aggregate bounds'],progress_credit=0),indent=1)+'\n')
