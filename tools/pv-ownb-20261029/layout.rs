use aspis_statement::pool_v1::pair_tree_hiding::{PoolV1PairCopyRowLinkV1 as Link,PoolV1PairCopyRowLinkKindV1 as Kind};
use std::mem::{size_of,align_of,offset_of};
fn check(kind:Kind,tag:u8,first:Option<u8>,second:Option<u8>){
 let x=Link{kind,producer_row:0x1234,consumer_row:0xabcd};
 assert_eq!((size_of::<Link>(),align_of::<Link>(),offset_of!(Link,kind),offset_of!(Link,producer_row),offset_of!(Link,consumer_row)),(8,2,4,0,2));
 // Read only compiler-pinned active fields. Never read padding or inactive payloads.
 let p=(&x as *const Link).cast::<u8>();
 unsafe {
  assert_eq!(*p,0x34); assert_eq!(*p.add(1),0x12);
  assert_eq!(*p.add(2),0xcd); assert_eq!(*p.add(3),0xab);
  assert_eq!(*p.add(4),tag);
  if let Some(a)=first {assert_eq!(*p.add(5),a)}
  if let Some(b)=second {assert_eq!(*p.add(6),b)}
 }
 assert!(!std::mem::needs_drop::<Link>());
}
fn main(){
 assert_eq!((size_of::<Kind>(),align_of::<Kind>()),(3,1));
 let mut cases=0;
 for a in 0..=255u8 {for b in 0..=255u8 {
  check(Kind::SpongeCarry{from:a,to:b},0,Some(a),Some(b));cases+=1;
 }}
 check(Kind::OwnerOutput,1,None,None);cases+=1;
 check(Kind::NullifierKey,2,None,None);cases+=1;
 check(Kind::InputSaltHead,3,None,None);cases+=1;
 check(Kind::InputSaltTail,4,None,None);cases+=1;
 for a in 0..=255u8 {check(Kind::PrivatePathCurrent{level:a},5,Some(a),None);cases+=1;}
 for a in 0..=255u8 {check(Kind::PrivatePathLeft{level:a},6,Some(a),None);cases+=1;}
 for a in 0..=255u8 {check(Kind::PrivatePathRight{level:a},7,Some(a),None);cases+=1;}
 for a in 0..=255u8 {check(Kind::ValueSource{value:a},8,Some(a),None);cases+=1;}
 check(Kind::ConservationInput,9,None,None);cases+=1;
 check(Kind::ConservationRecipient,10,None,None);cases+=1;
 check(Kind::ConservationChange,11,None,None);cases+=1;
 check(Kind::ConservationPartial,12,None,None);cases+=1;
 check(Kind::InputSecondCommitment,13,None,None);cases+=1;
 check(Kind::InputSelectedSide,14,None,None);cases+=1;
 check(Kind::OutputSecondCommitment,15,None,None);cases+=1;
 check(Kind::OutputPairFirst,16,None,None);cases+=1;
 check(Kind::OutputPairFirstWithdrawal,17,None,None);cases+=1;
 check(Kind::OutputPairSecond,18,None,None);cases+=1;
 for a in 0..=255u8 {check(Kind::AppendCurrentLeft{level:a},19,Some(a),None);cases+=1;}
 for a in 0..=255u8 {check(Kind::AppendCurrentRight{level:a},20,Some(a),None);cases+=1;}
 println!("active-field finite layout cases={cases}; no padding read; reclassification within existing tool trust");
}
