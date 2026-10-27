// Bounded source control slices; not installed-function equivalence.
#[kani::proof]
fn tail_mask_index() {
 let row:u16=kani::any();kani::assume(row>=768&&row<1024);
 let block=row>>4;let bit=row&15;
 assert!(block>=48&&block<64);assert!(bit<16);
 assert_eq!(block*16+bit,row);
}
#[kani::proof]
fn mask_dedup() {
 let mask:u16=kani::any();let bit:u8=kani::any();kani::assume(bit<16);
 let once=mask | (1u16<<bit);let twice=once | (1u16<<bit);
 assert_eq!(once,twice);
}
#[kani::proof]
fn mask_sort_swap() {
 let mask:u16=kani::any();let a:u8=kani::any();let b:u8=kani::any();
 kani::assume(a<16&&b<16);
 assert_eq!((mask|(1u16<<a))|(1u16<<b),(mask|(1u16<<b))|(1u16<<a));
}
#[kani::proof]
fn static_slot_guard() {
 let row:u16=kani::any();let arity:u8=kani::any();
 let rejected=row>=1024||arity>=2;
 if !rejected {assert!(row<1024);assert!(arity<2);assert!(arity+1<=2);}
 if arity==2 {assert!(rejected);}
}
#[kani::proof]
fn zero_weight_overwrite() {
 let second:u32=kani::any();let mut weights=[0u32;2];
 let first_slot=weights.iter().position(|x|*x==0).unwrap();
 weights[first_slot]=0;
 let second_slot=weights.iter().position(|x|*x==0).unwrap();
 weights[second_slot]=second;
 assert_eq!(first_slot,0);assert_eq!(second_slot,0);assert_eq!(weights[1],0);
}
#[kani::proof]
#[kani::unwind(5)]
fn guard_no_early_exit() {
 let comparisons:[bool;4]=kani::any();let mut clear=true;let mut count=0u8;
 for x in comparisons {clear &= x;count+=1;}
 assert_eq!(count,4);assert_eq!(clear,comparisons[0]&&comparisons[1]&&comparisons[2]&&comparisons[3]);
}
