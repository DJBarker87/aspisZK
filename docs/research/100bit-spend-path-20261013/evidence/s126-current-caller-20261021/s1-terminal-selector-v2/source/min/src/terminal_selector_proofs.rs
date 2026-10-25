use super::*;
fn row()->[QM31;29]{let mut a=[QM31::ZERO;29];let mut i=0;while i<29{a[i]=QM31{c0:CM31{a:M31(kani::any::<u32>()),b:M31(kani::any::<u32>())},c1:CM31{a:M31(kani::any::<u32>()),b:M31(kani::any::<u32>())}};i+=1;}a}
fn same(a:QM31,b:QM31){assert!(a.c0.a==b.c0.a);assert!(a.c0.b==b.c0.b);assert!(a.c1.a==b.c1.a);assert!(a.c1.b==b.c1.b);}
#[kani::proof]
#[kani::unwind(85)]
fn terminal_selector_native_copy_exact(){let input=[row(),row(),row()];let a=native_selector(&input);let b=copy_selector(&input);let mut i=0;while i<84{same(a[i],b[i]);same(a[i],input[i/28][i%28]);i+=1;}assert!(!core::mem::needs_drop::<QM31>());}
