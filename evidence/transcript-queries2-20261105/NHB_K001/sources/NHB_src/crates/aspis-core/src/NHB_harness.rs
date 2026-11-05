use super::*;
fn NHB_contains_ref(a: &[u32;22], n: usize, x:u32)->bool {
 let mut found=false;
 for i in 0..22 { if i<n {found |= a[i]==x;} }
 found
}
#[kani::requires(n<=22)]
#[kani::ensures(|out| *out == NHB_contains_ref(a,n,x))]
fn NHB_contains(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..n].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains)]
#[kani::unwind(24)]
fn NHB_contains_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains(&a,n,x);
}
