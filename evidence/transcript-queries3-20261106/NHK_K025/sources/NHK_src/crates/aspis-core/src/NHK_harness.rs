use super::*;
fn NHK_contains(a:&[u32;22],x:u32)->bool {
 let result=a[..14].contains(&x);
 #[cfg(not(NHK_invert))] {result}
 #[cfg(NHK_invert)] {!result}
}
#[kani::proof] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHK_contains_contract() {
 let a:[u32;22]=[kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any()];let x:u32=kani::any();
 let left=(a[0]==x) | (a[1]==x) | (a[2]==x) | (a[3]==x) | (a[4]==x) | (a[5]==x) | (a[6]==x) | (a[7]==x);let right=(a[8]==x) | (a[9]==x) | (a[10]==x) | (a[11]==x) | (a[12]==x) | (a[13]==x);
 let expected=left || right;let result=NHK_contains(&a,x);
 assert!(result==expected);
}
