use super::*;
fn NHK_contains(a:&[u32;22],offset:usize,x:u32)->bool {
 let result=a[offset..offset+4].contains(&x);
 #[cfg(not(NHK_invert))] {result}
 #[cfg(NHK_invert)] {!result}
}
#[kani::proof] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHK_contains_contract() {
 let a:[u32;22]=[kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any()];let x:u32=kani::any();let offset:usize=kani::any();
 kani::assume(offset<=18 && x<(1<<18) && a[0]<(1<<18) && a[1]<(1<<18) && a[2]<(1<<18) && a[3]<(1<<18) && a[4]<(1<<18) && a[5]<(1<<18) && a[6]<(1<<18) && a[7]<(1<<18) && a[8]<(1<<18) && a[9]<(1<<18) && a[10]<(1<<18) && a[11]<(1<<18) && a[12]<(1<<18) && a[13]<(1<<18) && a[14]<(1<<18) && a[15]<(1<<18) && a[16]<(1<<18) && a[17]<(1<<18) && a[18]<(1<<18) && a[19]<(1<<18) && a[20]<(1<<18) && a[21]<(1<<18) && true);
 let expected=a[offset+0]==x || a[offset+1]==x || a[offset+2]==x || a[offset+3]==x;
 let result=NHK_contains(&a,offset,x);
 assert!(result==expected);
}
