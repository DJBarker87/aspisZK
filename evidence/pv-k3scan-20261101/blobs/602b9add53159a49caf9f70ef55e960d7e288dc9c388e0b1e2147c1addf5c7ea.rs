//! Public permutation and checked index interfaces; no field geometry claim.
use aspis_core::r0::{domain::{FibreIndex,SlotIndex,InitialIndex,child_index,parent_index,slot_index,rev18},Error,FIBRE_COUNT,WORD_LEN};
use super::transport::Variant;
#[kani::proof]
#[kani::unwind(25)]
fn s2_row_and_tags() {
 let j:usize=kani::any();kani::assume(j<1024);
 let expected=((j&3)<<6)|(((j>>2)&3)<<8)|(((j>>4)&3)<<4)|((j>>6)&3)|(((j>>8)&3)<<2);
 let row=Variant::S2.row(j);assert_eq!(row,expected);assert!(row<1024);assert_eq!(Variant::S2.row(row),j);
 assert_eq!(Variant::S1.tag(),1);assert_eq!(Variant::S2.tag(),2);assert_eq!(Variant::D.tag(),3);
 let tag:u8=kani::any();let got=Variant::from_tag(tag);
 assert_eq!(got,match tag {1=>Some(Variant::S1),2=>Some(Variant::S2),3=>Some(Variant::D),_=>None});
}
#[kani::proof]
#[kani::unwind(25)]
fn checked_indices_and_reverse() {
 let u:usize=kani::any();let s:usize=kani::any();let i:usize=kani::any();
 match FibreIndex::new(u) {
  Ok(f)=>{assert!(u<FIBRE_COUNT);assert_eq!(f.get(),u);
   let mut expected=0usize;for bit in 0..18 {expected|=((u>>bit)&1)<<(17-bit);}
   assert_eq!(rev18(f),expected);assert!(expected<FIBRE_COUNT);
   if let Ok(slot)=SlotIndex::new(s) {
    assert!(s<4);assert_eq!(slot.get(),s);let child=child_index(f,slot);assert_eq!(child.get(),4*u+s);assert!(child.get()<WORD_LEN);
    assert_eq!(parent_index(child).get(),u);assert_eq!(slot_index(child).get(),s);
   } else {assert!(s>=4);}
  },Err(e)=>{assert!(u>=FIBRE_COUNT);assert_eq!(e,Error::IndexOutOfRange);}
 }
 match SlotIndex::new(s) {Ok(slot)=>{assert!(s<4);assert_eq!(slot.get(),s);},Err(e)=>{assert!(s>=4);assert_eq!(e,Error::IndexOutOfRange);}}
 match InitialIndex::new(i) {Ok(index)=>{assert!(i<WORD_LEN);assert_eq!(index.get(),i);},Err(e)=>{assert!(i>=WORD_LEN);assert_eq!(e,Error::IndexOutOfRange);}}
}
