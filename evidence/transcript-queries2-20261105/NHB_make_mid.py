from pathlib import Path
E=Path(__file__).resolve().parent
canon=' && '.join(f'a[{i}]<(1<<18)' for i in range(15))
absent=' && '.join(f'(n<={i} || a[{i}]!=x)' for i in range(15))
s='''use super::*;
fn NHB_absent_ref(a:&[u32;15],n:usize,x:u32)->bool {'''+absent+'''}
#[kani::requires(11<=n && n<=15 && x<(1<<18) && '''+canon+''' && NHB_absent_ref(&a,n,x))]
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
#[kani::requires(11<=n && n<=15 && witness<n && a[witness]==x && x<(1<<18) && '''+canon+''')]
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
'''
(E/'NHB_mid.rs.txt').write_text(s)
