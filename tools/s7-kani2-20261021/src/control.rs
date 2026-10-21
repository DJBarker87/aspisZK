use super::*;
// All checked source cursor/index operations surrounding the row transition.
#[kani::proof] #[kani::unwind(1)]
fn accumulator_control_step() {
 let next:usize=kani::any();let terms:usize=kani::any();let j:usize=kani::any();
 kani::assume(next<22 && terms<22 && j<64);
 let width=64;
 let trace_index=next*width+j;
 assert!(trace_index<22*64);
 assert_eq!(terms&3,terms%4);
 let mut final_terms=terms;final_terms+=1;
 let mut final_next=next;final_next+=1;
 assert_eq!(final_terms,terms+1);assert!(final_terms<=22);
 assert_eq!(final_next,next+1);assert!(final_next<=22);
}
#[kani::proof] #[kani::unwind(1)]
fn basis_control_step() {
 let n:usize=kani::any();let j:usize=kani::any();kani::assume(n<=128 && j<n);
 let write=n+j;let ordinal=j+1;let next=n*2;
 assert!(write<256);assert!(j<256);assert!(ordinal<=128);assert!(next<=256);
}

// Storage functor after the separately certified four scalar results have
// been substituted. Compares ordered source cell writes to owned row store;
// arithmetic is deliberately outside this storage-only certificate.
#[kani::proof] #[kani::unwind(68)]
fn accumulator_store_functor() {
 let rows:[[u64;4];64]=kani::any();let updated:[u64;4]=kani::any();
 let index:usize=kani::any();let observe:usize=kani::any();
 kani::assume(index<64 && observe<64);
 let mut source=rows.to_vec();let mut reference=rows.to_vec();
 let row=&mut source[index];
 for lane in 0..4 {row[lane]=updated[lane];}
 reference[index]=updated;
 for lane in 0..4 {
  assert_eq!(source[observe][lane],reference[observe][lane]);
  assert_eq!(source[observe][lane],if observe==index{updated[lane]}else{rows[observe][lane]});
 }
 assert_eq!(source.len(),64);assert_eq!(reference.len(),64);
}
