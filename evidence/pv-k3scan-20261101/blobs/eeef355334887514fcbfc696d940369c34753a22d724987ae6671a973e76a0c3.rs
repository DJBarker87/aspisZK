use super::equivalence16::qs;
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn sum_high_nodes() {let h=qs();let l=qs();let ranges=[4..25,33..57];let a=crate::host_terminal::access16::sum(h,l,&ranges);let mut b=crate::reference_terminal::access16::sum(h,l,&ranges);assert_eq!(a,b);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn sum_high_nodes_wrong() {let h=qs();let l=qs();let ranges=[4..25,33..57];let a=crate::host_terminal::access16::sum(h,l,&ranges);let mut b=crate::reference_terminal::access16::sum(h,l,&ranges);b.c0.a.0^=1;assert_eq!(a,b);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn sum_high_path() {let h=qs();let l=qs();let ranges=[57..63];let a=crate::host_terminal::access16::sum(h,l,&ranges);let mut b=crate::reference_terminal::access16::sum(h,l,&ranges);assert_eq!(a,b);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn sum_high_path_wrong() {let h=qs();let l=qs();let ranges=[57..63];let a=crate::host_terminal::access16::sum(h,l,&ranges);let mut b=crate::reference_terminal::access16::sum(h,l,&ranges);b.c0.a.0^=1;assert_eq!(a,b);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn sum_high_zero_57() {let h=qs();let l=qs();let ranges=[0..57];let a=crate::host_terminal::access16::sum(h,l,&ranges);let mut b=crate::reference_terminal::access16::sum(h,l,&ranges);assert_eq!(a,b);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn sum_high_zero_57_wrong() {let h=qs();let l=qs();let ranges=[0..57];let a=crate::host_terminal::access16::sum(h,l,&ranges);let mut b=crate::reference_terminal::access16::sum(h,l,&ranges);b.c0.a.0^=1;assert_eq!(a,b);}
