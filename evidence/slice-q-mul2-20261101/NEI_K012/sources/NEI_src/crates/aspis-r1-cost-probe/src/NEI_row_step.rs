use super::*;
// Native constructor, arbitrary advance, next, write and borrow restoration.
// No product or field operation is reached. The row is the actual full array.
#[kani::proof]
#[kani::unwind(7)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEI_copy::KMX_copy_nonoverlapping)]
fn iterator_context() {
 let before:[u64;4]=kani::any(); let mut row=before;
 let offset:usize=kani::any(); kani::assume(offset<=4);
 let replacement:u64=kani::any();
 let reply;
 {
  let mut it=(&mut row).into_iter();
  for _ in 0..offset { let _ = it.next().unwrap(); }
  assert_eq!(it.len(),4-offset);
  reply=match it.next() {
   Some(word)=>{let old=*word; *word=replacement; Some(old)},
   None=>None
  };
  assert_eq!(it.len(),4-offset-usize::from(offset<4));
 }
 if offset<4 {assert_eq!(reply,Some(before[offset]));}else{assert_eq!(reply,None);}
 let at:usize=kani::any(); kani::assume(at<4);
 let expected=if at==offset {replacement}else{before[at]};
 assert_eq!(row[at],if cfg!(NEI_wrong_iterator){expected^1}else{expected});
}
#[kani::proof]
#[kani::unwind(7)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEI_copy::KMX_copy_nonoverlapping)]
fn copy_row_window() {
 let before:[u64;4]=kani::any();let after=before;
 let at:usize=kani::any();kani::assume(at<4);
 assert_eq!(after[at],if cfg!(NEI_wrong_row_copy){before[at]^1}else{before[at]});
}
