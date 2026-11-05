use super::*;
fn NHK_contains_ref(a:&[u32;22],n:usize,x:u32)->bool {(n>0 && a[0]==x) || (n>1 && a[1]==x) || (n>2 && a[2]==x) || (n>3 && a[3]==x) || (n>4 && a[4]==x) || (n>5 && a[5]==x) || (n>6 && a[6]==x) || (n>7 && a[7]==x) || (n>8 && a[8]==x) || (n>9 && a[9]==x) || (n>10 && a[10]==x) || (n>11 && a[11]==x) || (n>12 && a[12]==x) || (n>13 && a[13]==x) || (n>14 && a[14]==x) || (n>15 && a[15]==x) || (n>16 && a[16]==x) || (n>17 && a[17]==x) || (n>18 && a[18]==x) || (n>19 && a[19]==x) || (n>20 && a[20]==x) || (n>21 && a[21]==x)}
#[kani::requires(n==14 && x<(1<<18) && a[0]<(1<<18) && a[1]<(1<<18) && a[2]<(1<<18) && a[3]<(1<<18) && a[4]<(1<<18) && a[5]<(1<<18) && a[6]<(1<<18) && a[7]<(1<<18) && a[8]<(1<<18) && a[9]<(1<<18) && a[10]<(1<<18) && a[11]<(1<<18) && a[12]<(1<<18) && a[13]<(1<<18) && a[14]<(1<<18) && a[15]<(1<<18) && a[16]<(1<<18) && a[17]<(1<<18) && a[18]<(1<<18) && a[19]<(1<<18) && a[20]<(1<<18) && a[21]<(1<<18) && (n>0 || a[0]==0) && (n>1 || a[1]==0) && (n>2 || a[2]==0) && (n>3 || a[3]==0) && (n>4 || a[4]==0) && (n>5 || a[5]==0) && (n>6 || a[6]==0) && (n>7 || a[7]==0) && (n>8 || a[8]==0) && (n>9 || a[9]==0) && (n>10 || a[10]==0) && (n>11 || a[11]==0) && (n>12 || a[12]==0) && (n>13 || a[13]==0) && (n>14 || a[14]==0) && (n>15 || a[15]==0) && (n>16 || a[16]==0) && (n>17 || a[17]==0) && (n>18 || a[18]==0) && (n>19 || a[19]==0) && (n>20 || a[20]==0) && (n>21 || a[21]==0) && expected==NHK_contains_ref(&a,n,x))]
#[kani::ensures(|out| *out==expected)]
fn NHK_contains(a:[u32;22],n:usize,x:u32,expected:bool)->bool {
 let result=a[..14].contains(&x);
 #[cfg(not(NHK_invert))] {result}
 #[cfg(NHK_invert)] {!result}
}
#[kani::proof_for_contract(NHK_contains)] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHK_contains_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();let expected:bool=kani::any();
 NHK_contains(a,n,x,expected);
}
