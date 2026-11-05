use super::*;
fn NHB_absent_ref(a:&[u32;22],n:usize,x:u32)->bool {
(n<=0 || a[0]!=x) && (n<=1 || a[1]!=x) && (n<=2 || a[2]!=x) && (n<=3 || a[3]!=x) && (n<=4 || a[4]!=x) && (n<=5 || a[5]!=x) && (n<=6 || a[6]!=x) && (n<=7 || a[7]!=x) && (n<=8 || a[8]!=x) && (n<=9 || a[9]!=x) && (n<=10 || a[10]!=x) && (n<=11 || a[11]!=x) && (n<=12 || a[12]!=x) && (n<=13 || a[13]!=x) && (n<=14 || a[14]!=x) && (n<=15 || a[15]!=x) && (n<=16 || a[16]!=x) && (n<=17 || a[17]!=x) && (n<=18 || a[18]!=x) && (n<=19 || a[19]!=x) && (n<=20 || a[20]!=x) && (n<=21 || a[21]!=x)
}
#[kani::requires(n<=22 && NHB_absent_ref(a,n,x))]
#[kani::ensures(|out| !*out)]
fn NHB_absent(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..n].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_absent)]
#[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_absent_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_absent(&a,n,x);
}
#[kani::requires(n<=22 && witness<n && a[witness]==x)]
#[kani::ensures(|out| *out)]
fn NHB_present(a:&[u32;22],n:usize,x:u32,witness:usize)->bool {
 let result=a[..n].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_present)]
#[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_present_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();let witness:usize=kani::any();
 NHB_present(&a,n,x,witness);
}
