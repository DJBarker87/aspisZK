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
fn NHB_contains_7(a:[u32;22],n:usize,x:u32)->bool {
 let result=a[..7].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_7)]
#[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_7_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_7(a,n,x);
}
#[kani::requires(n==8)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x))]
fn NHB_contains_8(a:[u32;22],n:usize,x:u32)->bool {
 let result=a[..8].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_8)]
#[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_8_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_8(a,n,x);
}
#[kani::requires(n==9)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x))]
fn NHB_contains_9(a:[u32;22],n:usize,x:u32)->bool {
 let result=a[..9].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_9)]
#[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_9_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_9(a,n,x);
}
#[kani::requires(n==10)]
#[kani::ensures(|out| *out == (a[0]==x || a[1]==x || a[2]==x || a[3]==x || a[4]==x || a[5]==x || a[6]==x || a[7]==x || a[8]==x || a[9]==x))]
fn NHB_contains_10(a:[u32;22],n:usize,x:u32)->bool {
 let result=a[..10].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains_10)]
#[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_10_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_10(a,n,x);
}
fn NHB_member(a:&[u32;22],n:usize,x:u32)->bool {match n {
0=>NHB_contains_0(a,n,x),
1=>NHB_contains_1(a,n,x),
2=>NHB_contains_2(a,n,x),
3=>NHB_contains_3(a,n,x),
4=>NHB_contains_4(a,n,x),
5=>NHB_contains_5(a,n,x),
6=>NHB_contains_6(a,n,x),
7=>NHB_contains_7(*a,n,x),
8=>NHB_contains_8(*a,n,x),
9=>NHB_contains_9(*a,n,x),
10=>NHB_contains_10(*a,n,x),
_=>unreachable!(),}}
impl QueryScan {
 fn NHB_direct_word(&mut self,candidate:u32)->bool {
            if self.accepted_len == QUERY_COUNT || self.draws == QUERY_MAX_DRAWS {
                return true;
            }
            self.draws += 1;
            if !NHB_member(&self.accepted,self.accepted_len,candidate) {
                self.accepted[self.accepted_len] = candidate;
                self.accepted_len += 1;
            }
 false
 }
}
fn NHB_natural_member(accepted:&[u32;22],len:usize,candidate:u32)->bool {(len>0 && accepted[0]==candidate) || (len>1 && accepted[1]==candidate) || (len>2 && accepted[2]==candidate) || (len>3 && accepted[3]==candidate) || (len>4 && accepted[4]==candidate) || (len>5 && accepted[5]==candidate) || (len>6 && accepted[6]==candidate) || (len>7 && accepted[7]==candidate) || (len>8 && accepted[8]==candidate) || (len>9 && accepted[9]==candidate) || (len>10 && accepted[10]==candidate) || (len>11 && accepted[11]==candidate) || (len>12 && accepted[12]==candidate) || (len>13 && accepted[13]==candidate) || (len>14 && accepted[14]==candidate) || (len>15 && accepted[15]==candidate) || (len>16 && accepted[16]==candidate) || (len>17 && accepted[17]==candidate) || (len>18 && accepted[18]==candidate) || (len>19 && accepted[19]==candidate) || (len>20 && accepted[20]==candidate) || (len>21 && accepted[21]==candidate)}
#[kani::proof] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub_verified(NHB_contains_0)]
#[kani::stub_verified(NHB_contains_1)]
#[kani::stub_verified(NHB_contains_2)]
#[kani::stub_verified(NHB_contains_3)]
#[kani::stub_verified(NHB_contains_4)]
#[kani::stub_verified(NHB_contains_5)]
#[kani::stub_verified(NHB_contains_6)]
#[kani::stub_verified(NHB_contains_7)]
#[kani::stub_verified(NHB_contains_8)]
#[kani::stub_verified(NHB_contains_9)]
#[kani::stub_verified(NHB_contains_10)]
fn NHB_native_word_contract() {
 let accepted:[u32;22]=kani::any();let len:usize=kani::any();let draws:usize=kani::any();
 let candidate:u32=kani::any();let window:usize=kani::any();
 kani::assume(len<=22 && draws<=64 && candidate<(1<<18) && window<22 && (draws<64 && len<=10) && accepted[0]<(1<<18) && accepted[1]<(1<<18) && accepted[2]<(1<<18) && accepted[3]<(1<<18) && accepted[4]<(1<<18) && accepted[5]<(1<<18) && accepted[6]<(1<<18) && accepted[7]<(1<<18) && accepted[8]<(1<<18) && accepted[9]<(1<<18) && accepted[10]<(1<<18) && accepted[11]<(1<<18) && accepted[12]<(1<<18) && accepted[13]<(1<<18) && accepted[14]<(1<<18) && accepted[15]<(1<<18) && accepted[16]<(1<<18) && accepted[17]<(1<<18) && accepted[18]<(1<<18) && accepted[19]<(1<<18) && accepted[20]<(1<<18) && accepted[21]<(1<<18) && (len>0 || accepted[0]==0) && (len>1 || accepted[1]==0) && (len>2 || accepted[2]==0) && (len>3 || accepted[3]==0) && (len>4 || accepted[4]==0) && (len>5 || accepted[5]==0) && (len>6 || accepted[6]==0) && (len>7 || accepted[7]==0) && (len>8 || accepted[8]==0) && (len>9 || accepted[9]==0) && (len>10 || accepted[10]==0) && (len>11 || accepted[11]==0) && (len>12 || accepted[12]==0) && (len>13 || accepted[13]==0) && (len>14 || accepted[14]==0) && (len>15 || accepted[15]==0) && (len>16 || accepted[16]==0) && (len>17 || accepted[17]==0) && (len>18 || accepted[18]==0) && (len>19 || accepted[19]==0) && (len>20 || accepted[20]==0) && (len>21 || accepted[21]==0));
 let member=NHB_natural_member(&accepted,len,candidate);let halted=len==22 || draws==64;
 let expected_len=if halted || member {len}else{len+1};let expected_draws=if halted{draws}else{draws+1};
 let expected_word=if !halted && !member && window==len {candidate}else{accepted[window]};
 let mut scan=QueryScan{accepted,accepted_len:len,draws};
 let mut copied_candidate=candidate;
 #[cfg(NHB_invert)] {copied_candidate^=1;}
 let stop=scan.NHB_direct_word(copied_candidate);
 assert!(stop==halted && scan.accepted_len==expected_len && scan.draws==expected_draws && scan.accepted[window]==expected_word);
}
