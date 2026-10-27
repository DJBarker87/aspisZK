use super::*;
// One source EbyKDot push versus the generic field multiplication model.
// Only one WideExact coordinate and the base scalar coordinate vary.
// Canonical, sparse domains; no whole-function/P6/source-extraction claim.
fn basis(limb:usize) {
 let x:u32=kani::any(); let y:u32=kani::any();
 kani::assume(x<=1); kani::assume(y<0x7fff_ffff);
 let mut limbs=[0u32;8];limbs[limb]=x;
 let e=E::from_limbs(limbs).unwrap();
 let scalar=K{c0:CM31{a:M31(y),b:M31(0)},c1:CM31::ZERO};
 let mut d=fast_pairing::EbyKDot::new();assert!(d.push(e,scalar).is_ok());
 assert_eq!(d.finish(),e.mul_qm31(scalar));
 kani::cover!(x!=0&&y!=0);
}
fn reject(limb:usize) {
 let x:u32=kani::any();kani::assume(x>=0x7fff_ffff);
 let mut a=[0u32;4];a[limb]=x;
 let scalar=K{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}};
 let mut d=fast_pairing::EbyKDot::new();assert!(d.push(E::ONE,scalar).is_err());
 assert_eq!(d.finish(),E::ZERO);kani::cover!(x==0xffff_ffff);
}
#[kani::proof] #[kani::unwind(10)] fn XRk_basis_0(){basis(0);}
#[kani::proof] #[kani::unwind(10)] fn XRk_basis_1(){basis(1);}
#[kani::proof] #[kani::unwind(10)] fn XRk_basis_2(){basis(2);}
#[kani::proof] #[kani::unwind(10)] fn XRk_basis_3(){basis(3);}
#[kani::proof] #[kani::unwind(10)] fn XRk_basis_4(){basis(4);}
#[kani::proof] #[kani::unwind(10)] fn XRk_basis_5(){basis(5);}
#[kani::proof] #[kani::unwind(10)] fn XRk_basis_6(){basis(6);}
#[kani::proof] #[kani::unwind(10)] fn XRk_basis_7(){basis(7);}
#[kani::proof] #[kani::unwind(10)] fn XRk_reject_0(){reject(0);}
#[kani::proof] #[kani::unwind(10)] fn XRk_reject_3(){reject(3);}
