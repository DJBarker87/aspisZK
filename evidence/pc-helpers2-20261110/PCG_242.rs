use super::*;
#[kani::proof]
fn scalar_full(){
 let mut p=RootHistoryPageV1{pool:[0;32],page_number:0,first_sequence:0,filled:0,roots:[[M31(0);8];256]};
 // Overwrite the sole field read after construction; no assertion depends on a page copy.
 let filled:u16=kani::any();p.filled=filled;
 assert!((p.is_full()==(filled==256))!=cfg!(PCG_NEG_PAGE));
}
#[kani::proof]
fn borrowed_get(){
 let mut p=RootHistoryPageV1{pool:[0;32],page_number:0,first_sequence:0,filled:0,roots:[[M31(0);8];256]};
 let page:u64=kani::any();let filled:u16=kani::any();let sequence:u64=kani::any();
 p.page_number=page;p.filled=filled;
 let location=root_history_location(sequence);
 assert!(location.slot<256);assert_eq!(location.page_number,sequence/256);assert_eq!(location.slot,(sequence%256) as u16);
 let got=p.get(sequence);
 if location.page_number!=page || location.slot>=filled {assert!(got.is_none());}
 else {let root=got.unwrap();let slot=usize::from(location.slot);let expected=unsafe{p.roots.as_ptr().add(if cfg!(PCG_NEG_PAGE){(slot+1)%256}else{slot})};assert!(core::ptr::eq(root,expected));}
}
