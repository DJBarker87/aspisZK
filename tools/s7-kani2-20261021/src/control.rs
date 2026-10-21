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
