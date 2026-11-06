use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn word(b:&[u8],i:usize)->u32 {u32::from_le_bytes([b[i],b[i+1],b[i+2],b[i+3]])}
// Actual frozen echeck, at most ONE complete chunk; arbitrary trailing bytes.
// The unbounded composition uses NJJ_Chunks and Lean first-error induction.
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn echeck_window(){
 let bytes:[u8;63]=kani::any();let n:usize=kani::any();kani::assume(n<=63);let k:bool=kani::any();
 let result=echeck(&bytes[..n],k);
 let mut good=true;
 if n>=32 {
  let words=[word(&bytes,0),word(&bytes,4),word(&bytes,8),word(&bytes,12),word(&bytes,16),word(&bytes,20),word(&bytes,24),word(&bytes,28)];
  for w in words {good=good&&w<2147483647;}
  if k {good=good&&words[4]==0&&words[5]==0&&words[6]==0&&words[7]==0;}
 }
 let expected=if good {Ok(())}else{Err(Error::Parse)};
 assert_eq!(result.is_ok(),expected.is_ok()^cfg!(NJZ_invert));
 if result.is_err(){assert_eq!(result,Err(Error::Parse));}
}

fn qm(words:[u32;4])->K {K{c0:aspis_core::field::CM31{a:M31(words[0]),b:M31(words[1])},c1:aspis_core::field::CM31{a:M31(words[2]),b:M31(words[3])}}}
struct ParseLog<'a>{expected:&'a[u8],reply:Option<E>,calls:usize}
impl ParseLog<'_>{fn parse(&mut self,c:&[u8])->Option<E>{
 assert_eq!(c.as_ptr(),self.expected.as_ptr());assert_eq!(c.len(),32);
 let j:usize=kani::any();kani::assume(j<32);assert_eq!(c[j],self.expected[j]);
 self.calls+=1;self.reply
}}
// Literal one-iteration echeck body; only its CLOSED parser call is a local oracle.
fn echeck_cut(c:&[u8],k:bool,log:&mut ParseLog)->Result<(),Error>{
 let x=log.parse(c).ok_or(Error::Parse)?;if k&&x.c1()!=K::ZERO{return Err(Error::Parse);} Ok(())
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn echeck_step(){
 let bytes:[u8;32]=kani::any();let low:[u32;4]=kani::any();let high:[u32;4]=kani::any();let some:bool=kani::any();let k:bool=kani::any();
 for w in low{kani::assume(w<2147483647);}for w in high{kani::assume(w<2147483647);}
 let reply=if some{Some(E::new(qm(low),qm(high)))}else{None};
 let mut log=ParseLog{expected:&bytes,reply,calls:0};let out=echeck_cut(&bytes,k,&mut log);
 let good=some&&(!k||high==[0;4]);assert_eq!(out.is_ok(),good^cfg!(NJZ_invert));
 if !good{assert_eq!(out,Err(Error::Parse));}assert_eq!(log.calls,1);assert_eq!(log.reply,reply);
}
type PD=[M31;8];
fn pd()->PD{core::array::from_fn(|_|M31(kani::any()))}
struct ParentLog{left:*const PD,right:*const PD,left_value:PD,right_value:PD,reply:PD,calls:usize}
impl ParentLog{fn compress(&mut self,l:&PD,r:&PD)->PD{
 assert_eq!(l as *const PD,self.left);assert_eq!(r as *const PD,self.right);
 assert_eq!(*l,self.left_value);assert_eq!(*r,self.right_value);self.calls+=1;self.reply
}}
// Literal format.rs tree_parent segment, sole child replaced by local log.
#[kani::requires(log.calls==0)]
#[kani::requires(log.left==left as *const PD && log.right==right as *const PD)]
#[kani::requires(log.left_value==*left && log.right_value==*right)]
#[kani::ensures(|out| *out==log.reply && log.calls==1 && !cfg!(NJZ_invert))]
#[kani::modifies(log)]
fn tree_parent_cut(left:&PD,right:&PD,log:&mut ParentLog)->PD{log.compress(left,right)}
#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree_parent(){
 let left=pd();let right=pd();let reply=pd();let mut log=ParentLog{left:&left,right:&right,left_value:left,right_value:right,reply,calls:0};
 let out=tree_parent_cut(&left,&right,&mut log);let mut expected=reply;if cfg!(NJZ_invert){expected[0].0^=1;}
 assert_eq!(out,expected);assert_eq!(log.calls,1);assert_eq!(left,log.left_value);assert_eq!(right,log.right_value);
}
#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn roots_step(){
 let mut roots:[PD;21]=core::array::from_fn(|_|pd());let before=roots;
 let level:usize=kani::any();let j:usize=kani::any();kani::assume(level<20&&j<21);let reply=pd();
 let mut log=ParentLog{left:&roots[level],right:&roots[level],left_value:roots[level],right_value:roots[level],reply,calls:0};
 // Literal single iteration of incremental_merkle.rs::pool_v1_empty_roots.
 roots[level+1]=tree_parent_cut(&roots[level],&roots[level],&mut log);
 let mut expected=if j==level+1{reply}else{before[j]};if cfg!(NJZ_invert){expected[0].0^=1;}
 assert_eq!(roots[j],expected);assert_eq!(log.calls,1);
}
#[kani::proof]
#[kani::unwind(25)]
fn roots_control(){
 let mut seen=[0usize;20];let mut count=0;for level in 0..20{seen[count]=level;count+=1;}
 let j:usize=kani::any();kani::assume(j<20);assert_eq!(seen[j],j^(if cfg!(NJZ_invert){1}else{0}));assert_eq!(count,20);
}
#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn empty_constructor(){
 let empty:[PD;21]=core::array::from_fn(|_|pd());
 // Literal constructor after the arbitrary full empty-roots child reply.
 let out=aspis_statement::pool_v1::incremental_merkle::IncrementalMerkleTreeV1{
 next_leaf_index:0,root:empty[20],frontier:core::array::from_fn(|level|empty[level])};
 let j:usize=kani::any();kani::assume(j<20);
 let mut expected=empty[j];if cfg!(NJZ_invert){expected[0].0^=1;}
 assert_eq!(out.next_leaf_index,0);assert_eq!(out.root,empty[20]);assert_eq!(out.frontier[j],expected);
}

#[kani::proof_for_contract(tree_parent_cut)]
#[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree_parent_contract(){
 let left=pd();let right=pd();let reply=pd();let mut log=ParentLog{left:&left,right:&right,left_value:left,right_value:right,reply,calls:0};
 let _out=tree_parent_cut(&left,&right,&mut log);
}
fn default_cut(reply:aspis_statement::pool_v1::incremental_merkle::IncrementalMerkleTreeV1)->aspis_statement::pool_v1::incremental_merkle::IncrementalMerkleTreeV1{reply}
#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn default_return(){
 let next:u64=kani::any();let root=pd();let frontier:[PD;20]=core::array::from_fn(|_|pd());
 let reply=aspis_statement::pool_v1::incremental_merkle::IncrementalMerkleTreeV1{next_leaf_index:next,root,frontier};
 let out=default_cut(reply);let j:usize=kani::any();kani::assume(j<20);let mut expected=frontier[j];if cfg!(NJZ_invert){expected[0].0^=1;}
 assert_eq!(out.next_leaf_index,next);assert_eq!(out.root,root);assert_eq!(out.frontier[j],expected);
}
fn raw_checkpoint<const N:usize>(){
 let bytes:[u8;1768]=kani::any();let start:usize=kani::any();kani::assume(start<=1768-N);let mut r=Reader{bytes:&bytes,at:start};let ptr=r.bytes.as_ptr();
 let out=r.raw::<N>();let j:usize=kani::any();let b:usize=kani::any();kani::assume(j<N&&b<1768);
 assert_eq!(out[j],bytes[start+j]^(if cfg!(NJZ_invert){1}else{0}));assert_eq!(r.at,start+N);assert_eq!(r.bytes.as_ptr(),ptr);assert_eq!(r.bytes.len(),1768);assert_eq!(r.bytes[b],bytes[b]);
}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn raw4_checkpoint(){raw_checkpoint::<4>();}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn raw16_checkpoint(){raw_checkpoint::<16>();}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn raw32_checkpoint(){raw_checkpoint::<32>();}

impl kani::Arbitrary for ParentLog{fn any()->Self{Self{left:kani::any::<usize>() as *const PD,right:kani::any::<usize>() as *const PD,left_value:pd(),right_value:pd(),reply:pd(),calls:kani::any()}}}
#[kani::ensures(|out| (out[0]==M31::ZERO)^cfg!(NJZ_inverse_ensures))]
#[kani::modifies(log)]
fn fidelity_weak(_left:&PD,_right:&PD,log:&mut ParentLog)->PD{log.calls=1;[M31::ZERO;8]}
fn fidelity_args()->(PD,PD,ParentLog){let left=pd();let right=pd();let log=ParentLog{left:&left,right:&right,left_value:left,right_value:right,reply:pd(),calls:0};(left,right,log)}
#[kani::proof_for_contract(fidelity_weak)]
#[kani::unwind(25)]
fn fidelity_contract(){let(l,r,mut log)=fidelity_args();let _out=fidelity_weak(&l,&r,&mut log);}
#[kani::proof]
#[kani::unwind(25)]
fn fidelity_real(){let(l,r,mut log)=fidelity_args();let out=fidelity_weak(&l,&r,&mut log);assert_eq!(out[1],M31::ZERO);}
#[kani::proof]
#[kani::unwind(25)]
#[kani::stub_verified(fidelity_weak)]
fn fidelity_unimplied(){let(l,r,mut log)=fidelity_args();let out=fidelity_weak(&l,&r,&mut log);assert_eq!(out[1],M31::ZERO);}
#[kani::ensures(|out| out[0]==M31::ZERO)]
#[kani::modifies(&mut log.calls)]
fn fidelity_modifies(_left:&PD,_right:&PD,log:&mut ParentLog)->PD{log.calls=1;if cfg!(NJZ_bad_modifies){log.reply[1]=M31(1);}[M31::ZERO;8]}
#[kani::proof_for_contract(fidelity_modifies)]
#[kani::unwind(25)]
fn fidelity_modifies_check(){let(l,r,mut log)=fidelity_args();let _out=fidelity_modifies(&l,&r,&mut log);}
