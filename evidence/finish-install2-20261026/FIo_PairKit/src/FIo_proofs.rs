use aspis_core::field::WideExact as E;
use crate::{weights,FIo_reference::{self as reference,Arithmetic}};
pub struct Actual;
impl Arithmetic for Actual {
 type E=E;
 fn zero()->E {E::ZERO}
 fn add(a:E,b:E)->E {a.add(b)}
 fn mul(a:E,b:E)->E {a.mul(b)}
 fn field(bytes:&[u8],i:usize)->E {weights::field(bytes,i)}
}
fn any_e()->E {
 let limbs:[u32;8]=kani::any();
 for x in limbs {kani::assume(x<2147483647);}
 E::from_limbs(limbs).unwrap()
}
#[kani::proof]
#[kani::unwind(66)]
fn FIo_grouped_exact() {
 let mut f=[0u8;2048];
 for j in 0..64 {f[j*32..(j+1)*32].copy_from_slice(&any_e().to_le_bytes());}
 let mut low=[E::ZERO;16];
 for j in 0..16 {low[j]=any_e();}
 assert_eq!(weights::s2_grouped_inactive_pair(&f,&low),reference::grouped::<Actual>(&f,low));
}
#[kani::proof]
#[kani::unwind(17)]
fn FIo_coefficient_exact() {
 let mut coefficients=[E::ZERO;12];
 for c in &mut coefficients {*c=any_e();}
 let j:usize=kani::any();kani::assume(j<64);
 let value=any_e();let mut original=coefficients;
 let group=reference::GROUPS[j] as usize;
 original[group]=original[group].add(value);
 assert_eq!(original,reference::coefficient::<Actual>(coefficients,j,value));
}
#[kani::proof]
#[kani::unwind(18)]
fn FIo_subset_exact() {
 let mut low=[E::ZERO;16];for c in &mut low {*c=any_e();}
 let mask:u16=kani::any();let mut original=E::ZERO;
 for bit in 0..16 {
  let challenge=low[bit];
  if mask&(1<<bit)!=0 {original=original.add(challenge);}
 }
 assert_eq!(original,reference::subset::<Actual>(low,mask));
}
