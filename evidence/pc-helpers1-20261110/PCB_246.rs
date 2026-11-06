use super::*;
#[path="PCB_reference.rs"] pub(super) mod reference;
#[kani::proof_for_contract(root_history_location)]
fn location_contract(){let _=root_history_location(kani::any());}

#[kani::ensures(|r| r.page_number == sequence/256)]
fn record_weak(sequence:u64)->RootHistoryLocationV1 {
 RootHistoryLocationV1 {page_number:sequence/256,slot:(sequence%256) as u16}
}
#[kani::proof_for_contract(record_weak)]
fn record_weak_contract(){let _=record_weak(kani::any());}
#[kani::proof]
fn record_real(){let n:u64=kani::any();assert_eq!(record_weak(n).slot,(n%256) as u16);}
#[kani::proof] #[kani::stub_verified(record_weak)]
fn record_unimplied(){let n:u64=kani::any();assert_eq!(record_weak(n).slot,(n%256) as u16);}
#[kani::modifies(&mut x[0])]
#[kani::ensures(|r| r.page_number==0)]
fn record_bad_frame(x:&mut [u16;2])->RootHistoryLocationV1 {
 x[1]=x[1].wrapping_add(1);RootHistoryLocationV1 {page_number:0,slot:0}
}
#[kani::proof_for_contract(record_bad_frame)]
fn record_frame(){let mut x:[u16;2]=kani::any();let _=record_bad_frame(&mut x);}
