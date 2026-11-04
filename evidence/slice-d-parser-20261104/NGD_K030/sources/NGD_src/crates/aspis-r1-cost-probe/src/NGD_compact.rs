use super::*;
#[kani::proof] #[kani::unwind(8)]
fn slot_all(){
 let slot:usize=kani::any();kani::assume(slot<=6);
 let result=slot_offset(slot);
 let expected=match slot{0=>28359,1=>33031,2=>37703,3=>41799,4=>47303,5=>52807,_=>57607};
 assert!((result==expected) != cfg!(NGD_invert));
}
#[kani::proof] #[kani::unwind(2)]
fn slot_native_step(){
 let i:usize=kani::any();let at:usize=kani::any();kani::assume(i<6&&at<=57607);
 let mut next=at;next+=32*SLOT_NODES[i];let j=i+1;
 assert!((next==at+match i{0|1=>4672,2=>4096,3|4=>5504,_=>4800}&&j<=6&&next<=63111) != cfg!(NGD_invert));
}

pub(super) fn slot_reference(slot:usize)->usize{let mut at=OFF_NODES;let mut i=0;while i<slot{at+=32*SLOT_NODES[i];i+=1;}at}
#[kani::proof_for_contract(slot_offset)] #[kani::unwind(8)]
fn slot_contract(){let slot:usize=kani::any();kani::assume(slot<=6);let _=slot_offset(slot);}
