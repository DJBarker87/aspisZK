#[cfg(kani)] mod proofs {
use super::*;
use std::cell::RefCell;
#[derive(Clone,Copy)] struct Oracle<'a>(&'a RefCell<O>);
struct O{initial:[u8;32],answers:[[u8;32];3],row:u8,record:Vec<u8>,next:usize}
impl Digest32 for Oracle<'_>{fn digest(&self,p:&[&[u8]])->[u8;32]{
 let mut s=self.0.borrow_mut();let i=s.next;assert!(i<3);
 if i==0 {assert_eq!(p.len(),3);assert_eq!(p[0],&s.initial);assert_eq!(p[1],&[0,0xa0+s.row]);assert_eq!(p[2],&s.record);}
 else {assert_eq!(p.len(),2);assert_eq!(p[0],&s.answers[0]);assert_eq!(p[1],&[i as u8]);}
 s.next+=1;s.answers[i]
}}
static mut SAMPLE:[u32;4]=[0;4];
fn common(block:&[u8;32])->QM31 { // Congruence cut: all four returned words are arbitrary.
 let _=block; let raw:[u32;4]=unsafe{SAMPLE};
 QM31{c0:field::CM31{a:field::M31(raw[0]),b:field::M31(raw[1])},c1:field::CM31{a:field::M31(raw[2]),b:field::M31(raw[3])}}
}
fn check_reachable<const N:usize,const PFX:usize>(row:u8,first_zc:bool){
 unsafe{SAMPLE=kani::any();}
 let payload:[u8;N]=kani::any();let initial:[u8;32]=kani::any();let next:u8=if first_zc {3} else {kani::any()};
 let mut prefix:[u8;PFX]=kani::any();
 if first_zc {
  assert_eq!(PFX,79);assert_eq!(row,3);assert_eq!(N,0);
  // Literal prior wire image: C1 || empty rows 0,1 || row-2 C2 record.
  for i in 32..42 {prefix[i]=0;}
  prefix[42]=1;prefix[43]=32;
  for i in 44..47 {prefix[i]=0;}
 }
 let framed=wire::record(row,&payload).unwrap_or_default();
 let cell=RefCell::new(O{initial,answers:kani::any(),row,record:framed,next:0});
 let mut state=SemanticTranscript{state:initial,hash:Oracle(&cell),next_row:next};
 let mut bytes=prefix.to_vec();let actual=native(row,&payload,&mut state,&mut bytes);let calls=cell.borrow().next;
 cell.borrow_mut().next=0;
 let (expect,st,out)=owned(row,payload.to_vec(),SemanticTranscript{state:initial,hash:Oracle(&cell),next_row:next},prefix.to_vec());
 assert_eq!(actual,expect);assert_eq!(state.state,st.state);assert_eq!(state.next_row,st.next_row);
 assert_eq!(cell.borrow().next,calls);assert_eq!(bytes.len(),out.len());
 let j:usize=kani::any();kani::assume(j<bytes.len());assert_eq!(bytes[j],out[j]);
}
fn check_prefix<const N:usize,const PFX:usize>(row:u8){check_reachable::<N,PFX>(row,false)}
fn check<const N:usize>(row:u8){check_prefix::<N,8>(row)}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_empty(){let row:u8=kani::any();kani::assume(row<25);check::<0>(row)}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_root(){check::<32>(2)}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_empty_fixed(){check::<0>(0)}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_empty_class(){let row:u8=kani::any();kani::assume(row<=13&&row!=2);check::<0>(row)}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_real_first(){check_prefix::<0,32>(0)}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_real_second(){check_prefix::<0,37>(1)}
#[kani::proof] #[kani::unwind(96)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_real_c2(){check_prefix::<32,42>(2)}
#[kani::proof] #[kani::unwind(160)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_real_zc_first(){check_prefix::<0,79>(3)}
#[kani::proof] #[kani::unwind(160)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_reachable_zc_first(){check_reachable::<0,79>(3,true)}
#[kani::proof] #[kani::unwind(192)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_real_mask(){check_prefix::<32,134>(14)}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_mask(){check::<32>(14)}
#[kani::proof] #[kani::unwind(940)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_round(){let row:u8=kani::any();kani::assume(row>=15&&row<=24);check::<896>(row)}
}
