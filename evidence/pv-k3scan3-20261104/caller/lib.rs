use aspis_core::field::{QM31,CM31,M31};
mod host; mod reference;
fn q()->QM31 {let x:[u32;4]=kani::any(); QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn qs<const N:usize>()->[QM31;N] {let mut a=[QM31::ZERO;N];let mut i=0;while i<N {a[i]=q();i+=1;}a}
fn check(a:QM31,b:QM31) {if cfg!(feature="negative-control") {assert_ne!(a,b);}else{assert_eq!(a,b);}}
mod equivalence17 {
 use super::*;
 #[kani::proof] #[kani::unwind(256)]
 fn sum_high_nodes() {let h=qs();let l=qs();let ranges=[4..25,33..57];let mut log=();let a=caller(h,l,&ranges,&mut log);check(a,reference::sum(h,l,&ranges));}
 #[kani::proof] #[kani::unwind(256)]
 fn sum_high_path() {let h=qs();let l=qs();let ranges=[57..63];let mut log=();let a=caller(h,l,&ranges,&mut log);check(a,reference::sum(h,l,&ranges));}
 // No mul/square child is reached by this frozen cone. Empty modifies/effect set.
 fn caller(h:[QM31;64],l:[QM31;16],r:&[core::ops::Range<usize>],_log:&mut ())->QM31 {host::sum(h,l,r)}
}

#[path="array.rs"] mod array;
