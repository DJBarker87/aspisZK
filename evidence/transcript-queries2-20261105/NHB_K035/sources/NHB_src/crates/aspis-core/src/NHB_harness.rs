use super::*;
fn NHB_absent_ref(a:&[u32;15],n:usize,x:u32)->bool {(n<=0 || a[0]!=x) && (n<=1 || a[1]!=x) && (n<=2 || a[2]!=x) && (n<=3 || a[3]!=x) && (n<=4 || a[4]!=x) && (n<=5 || a[5]!=x) && (n<=6 || a[6]!=x) && (n<=7 || a[7]!=x) && (n<=8 || a[8]!=x) && (n<=9 || a[9]!=x) && (n<=10 || a[10]!=x) && (n<=11 || a[11]!=x) && (n<=12 || a[12]!=x) && (n<=13 || a[13]!=x) && (n<=14 || a[14]!=x)}
#[kani::requires(11<=n && n<=15 && x<(1<<18) && a[0]<(1<<18) && a[1]<(1<<18) && a[2]<(1<<18) && a[3]<(1<<18) && a[4]<(1<<18) && a[5]<(1<<18) && a[6]<(1<<18) && a[7]<(1<<18) && a[8]<(1<<18) && a[9]<(1<<18) && a[10]<(1<<18) && a[11]<(1<<18) && a[12]<(1<<18) && a[13]<(1<<18) && a[14]<(1<<18) && NHB_absent_ref(&a,n,x))]
#[kani::ensures(|out| !*out)]
fn NHB_absent(a:[u32;15],n:usize,x:u32)->bool {
 let result=a[..n].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_absent)] #[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_absent_contract() {
 let a:[u32;15]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_absent(a,n,x);
}
#[kani::requires(11<=n && n<=15 && witness<n && a[witness]==x && x<(1<<18) && a[0]<(1<<18) && a[1]<(1<<18) && a[2]<(1<<18) && a[3]<(1<<18) && a[4]<(1<<18) && a[5]<(1<<18) && a[6]<(1<<18) && a[7]<(1<<18) && a[8]<(1<<18) && a[9]<(1<<18) && a[10]<(1<<18) && a[11]<(1<<18) && a[12]<(1<<18) && a[13]<(1<<18) && a[14]<(1<<18))]
#[kani::ensures(|out| *out)]
fn NHB_present(a:[u32;15],n:usize,x:u32,witness:usize)->bool {
 let result=a[..n].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_present)] #[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_present_contract() {
 let a:[u32;15]=kani::any();let n:usize=kani::any();let x:u32=kani::any();let witness:usize=kani::any();
 NHB_present(a,n,x,witness);
}
