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
// Caller allocation: BatchedWeights::new allocates exactly 64 four-word rows.
// One arbitrary mutable index, row result and disjoint row/lane window.
#[kani::proof]
#[kani::unwind(68)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEI_copy::KMX_copy_nonoverlapping)]
fn vector_row_context() {
 let mut raw=kani::vec::exact_vec::<[u64;4],64>();
 let index:usize=kani::any(); let at:usize=kani::any();let lane:usize=kani::any();
 kani::assume(index<64 && at<64 && lane<4);
 let before=raw[at][lane];let old=raw[index];
 let replacement:[u64;4]=kani::any();let reply;
 let pointer=raw.as_ptr();let capacity=raw.capacity();
 {let row=&mut raw[index];reply=*row;*row=replacement;}
 assert_eq!(reply,old);
 assert!(raw.len()==64 && raw.capacity()==capacity && raw.as_ptr()==pointer);
 let expected=if at==index {replacement[lane]}else{before};
 assert_eq!(raw[at][lane],if cfg!(NEI_wrong_vector_row){expected^1}else{expected});
}
// Genuine split of timed-out vector_row_context: Vec-to-slice borrow geometry.
#[kani::proof] #[kani::unwind(68)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEI_copy::KMX_copy_nonoverlapping)]
fn vector_row_geometry() {
 let mut raw=kani::vec::exact_vec::<[u64;4],64>();
 let index:usize=kani::any();kani::assume(index<64);
 let pointer=raw.as_mut_ptr();let capacity=raw.capacity();
 let got={let row=&mut raw[index];row as *mut [u64;4]};
 let expected=unsafe{pointer.add(if cfg!(NEI_wrong_row_geometry){(index+1)%64}else{index})};
 assert_eq!(got,expected);
 assert!(raw.as_mut_ptr()==pointer && raw.len()==64 && raw.capacity()==capacity);
}
// Other split: one arbitrary native nested-slice write and disjoint window.
#[kani::proof] #[kani::unwind(68)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEI_copy::KMX_copy_nonoverlapping)]
fn slice_row_lane() {
 let before:[[u64;4];64]=kani::any();let mut rows=before;
 let index:usize=kani::any();let lane:usize=kani::any();let at:usize=kani::any();let col:usize=kani::any();
 kani::assume(index<64 && at<64 && lane<4 && col<4);
 let value:u64=kani::any();let old;
 {let slice:&mut [[u64;4]]=&mut rows;let row=&mut slice[index];old=row[lane];row[lane]=value;}
 assert_eq!(old,before[index][lane]);
 let expected=if index==at && lane==col {value}else{before[at][col]};
 assert_eq!(rows[at][col],if cfg!(NEI_wrong_slice_row){expected^1}else{expected});
}

// Further isolation: one before-window, no full 2 KiB carrier duplication.
#[kani::proof] #[kani::unwind(68)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEI_copy::KMX_copy_nonoverlapping)]
fn slice_row_write_window() {
 let mut rows:[[u64;4];64]=kani::any();
 let index:usize=kani::any();let lane:usize=kani::any();let at:usize=kani::any();let col:usize=kani::any();
 kani::assume(index<64 && at<64 && lane<4 && col<4);
 let before=rows[at][col];let selected=rows[index][lane];let replacement:u64=kani::any();let reply;
 {let slice:&mut [[u64;4]]=&mut rows;let row=&mut slice[index];let word=&mut row[lane];reply=*word;*word=replacement;}
 assert_eq!(reply,selected);
 let expected=if index==at && lane==col {replacement}else{before};
 assert_eq!(rows[at][col],if cfg!(NEI_wrong_slice_window){expected^1}else{expected});
}
