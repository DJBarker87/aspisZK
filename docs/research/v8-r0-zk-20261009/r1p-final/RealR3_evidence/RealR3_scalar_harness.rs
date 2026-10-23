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
fn check<const N:usize>(row:u8){
 unsafe{SAMPLE=kani::any();}
 let payload:[u8;N]=kani::any();let initial:[u8;32]=kani::any();let next:u8=kani::any();
 let prefix:[u8;8]=kani::any();
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
#[kani::proof] #[kani::unwind(40)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_empty(){let row:u8=kani::any();kani::assume(row<25);check::<0>(row)}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_root(){check::<32>(2)}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_empty_fixed(){check::<0>(0)}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_empty_class(){let row:u8=kani::any();kani::assume(row<=13&&row!=2);check::<0>(row)}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_mask(){check::<32>(14)}
#[kani::proof] #[kani::unwind(940)] #[kani::stub(crate::sampler::qm31_sample,common)] fn scalar_round(){let row:u8=kani::any();kani::assume(row>=15&&row<=24);check::<896>(row)}
}
