use super::*;
#[kani::requires(n==0)]
#[kani::ensures(|out| *out == (false))]
fn NHB_contains_0(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..0].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_0)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_0_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_0(&a,n,x);
}
#[kani::requires(n==1)]
#[kani::ensures(|out| *out == (a[0]==x))]
fn NHB_contains_1(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..1].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_1)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_1_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_1(&a,n,x);
}
#[kani::requires(n==2)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x))]
fn NHB_contains_2(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..2].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_2)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_2_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_2(&a,n,x);
}
#[kani::requires(n==3)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x))]
fn NHB_contains_3(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..3].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_3)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_3_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_3(&a,n,x);
}
#[kani::requires(n==4)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x))]
fn NHB_contains_4(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..4].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_4)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_4_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_4(&a,n,x);
}
#[kani::requires(n==5)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x))]
fn NHB_contains_5(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..5].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_5)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_5_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_5(&a,n,x);
}
#[kani::requires(n==6)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x))]
fn NHB_contains_6(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..6].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_6)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_6_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_6(&a,n,x);
}
#[kani::requires(n==7)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x))]
fn NHB_contains_7(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..7].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_7)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_7_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_7(&a,n,x);
}
#[kani::requires(n==8)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x))]
fn NHB_contains_8(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..8].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_8)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_8_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_8(&a,n,x);
}
#[kani::requires(n==9)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x))]
fn NHB_contains_9(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..9].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_9)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_9_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_9(&a,n,x);
}
#[kani::requires(n==10)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x))]
fn NHB_contains_10(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..10].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_10)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_10_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_10(&a,n,x);
}
#[kani::requires(n==11)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x || a[10]==x))]
fn NHB_contains_11(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..11].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_11)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_11_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_11(&a,n,x);
}
#[kani::requires(n==12)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x || a[10]==x || a[11]==x))]
fn NHB_contains_12(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..12].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_12)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_12_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_12(&a,n,x);
}
#[kani::requires(n==13)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x || a[10]==x || a[11]==x || a[12]==x))]
fn NHB_contains_13(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..13].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_13)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_13_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_13(&a,n,x);
}
#[kani::requires(n==14)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x || a[10]==x || a[11]==x || a[12]==x || a[13]==x))]
fn NHB_contains_14(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..14].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_14)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_14_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_14(&a,n,x);
}
#[kani::requires(n==15)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x || a[10]==x || a[11]==x || a[12]==x || a[13]==x || a[14]==x))]
fn NHB_contains_15(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..15].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_15)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_15_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_15(&a,n,x);
}
#[kani::requires(n==16)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x || a[10]==x || a[11]==x || a[12]==x || a[13]==x || a[14]==x || a[15]==x))]
fn NHB_contains_16(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..16].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_16)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_16_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_16(&a,n,x);
}
#[kani::requires(n==17)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x || a[10]==x || a[11]==x || a[12]==x || a[13]==x || a[14]==x || a[15]==x || a[16]==x))]
fn NHB_contains_17(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..17].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_17)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_17_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_17(&a,n,x);
}
#[kani::requires(n==18)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x || a[10]==x || a[11]==x || a[12]==x || a[13]==x || a[14]==x || a[15]==x || a[16]==x || a[17]==x))]
fn NHB_contains_18(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..18].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_18)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_18_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_18(&a,n,x);
}
#[kani::requires(n==19)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x || a[10]==x || a[11]==x || a[12]==x || a[13]==x || a[14]==x || a[15]==x || a[16]==x || a[17]==x || a[18]==x))]
fn NHB_contains_19(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..19].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_19)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_19_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_19(&a,n,x);
}
#[kani::requires(n==20)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x || a[10]==x || a[11]==x || a[12]==x || a[13]==x || a[14]==x || a[15]==x || a[16]==x || a[17]==x || a[18]==x || a[19]==x))]
fn NHB_contains_20(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..20].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_20)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_20_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_20(&a,n,x);
}
#[kani::requires(n==21)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x || a[10]==x || a[11]==x || a[12]==x || a[13]==x || a[14]==x || a[15]==x || a[16]==x || a[17]==x || a[18]==x || a[19]==x || a[20]==x))]
fn NHB_contains_21(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..21].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_21)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_21_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_21(&a,n,x);
}
#[kani::requires(n==22)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x || a[10]==x || a[11]==x || a[12]==x || a[13]==x || a[14]==x || a[15]==x || a[16]==x || a[17]==x || a[18]==x || a[19]==x || a[20]==x || a[21]==x))]
fn NHB_contains_22(a:&[u32;22],n:usize,x:u32)->bool {
 let result=a[..22].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_22)]
#[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_22_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_22(&a,n,x);
}
