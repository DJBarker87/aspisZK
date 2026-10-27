use super::*;
use alloc::{boxed::Box,vec};
fn any_k()->K {
    let x:[u32;4]=kani::any();
    kani::assume(x.iter().all(|v|*v<0x7fff_ffff));
    K{c0:aspis_core::field::CM31{a:M31(x[0]),b:M31(x[1])},c1:aspis_core::field::CM31{a:M31(x[2]),b:M31(x[3])}}
}
fn any_e()->E {
    let x:[u32;8]=kani::any();
    kani::assume(x.iter().all(|v|*v<0x7fff_ffff));E::from_limbs(x).unwrap()
}
fn sha256(parts:&[&[u8]])->[u8;32] {
    use sha2::{Digest,Sha256};let mut h=Sha256::new();for p in parts {h.update(p)}h.finalize().into()
}
fn semantic()->r1_semantic::Verified<aspis_core::digest::LegacyHashFn> {
    let hash=aspis_core::digest::LegacyHashFn(sha256);
    let zero=K::ZERO;
    r1_semantic::Verified {
      roots:[[0;32];2],challenges:aspis_r1_cost_probe::r1_wire::Challenges{lambda:zero,chi:zero,theta:zero,zc:[zero;10],mu:zero,eta:zero},
      alpha:[zero;10],claims:Box::new(core::array::from_fn(|_|core::array::from_fn(|_|any_k()))),
      extra:core::array::from_fn(|_|any_k()),before_z1:core::array::from_fn(|_|any_k()),
      state_before_z0:[0;32],z:[aspis_core::circle::SecureCirclePoint{x:zero,y:zero};2],
      transcript:aspis_r1_cost_probe::r1_wire::SemanticTranscript::new(hash,&[],&[0;32]).unwrap(),
    }
}
#[kani::proof]
#[kani::unwind(32)]
fn XRe_prepared_whole() {
    let sem=semantic();let g=core::array::from_fn(|_|any_e());let inactive=any_e();let kappa=any_e();
    let mut y1=[0u8;928];for i in 0..29 {y1[32*i..32*i+32].copy_from_slice(&any_e().to_le_bytes())}
    assert_eq!(XRe_shipped_prepared_claim(&sem,&y1,inactive,&g,kappa),XRe_reference_prepared_claim(&sem,&y1,inactive,&g,kappa));
}
#[kani::proof]
#[kani::unwind(40)]
fn XRe_checkpoint_put() {let e=any_e();let mut a=vec![kani::any()];let mut b=a.clone();XRe_shipped_put(&mut a,e);XRe_reference_put(&mut b,e);assert_eq!(a,b);}
#[kani::proof]
#[kani::unwind(24)]
fn XRe_checkpoint_put_k() {let k=any_k();let mut a=vec![kani::any()];let mut b=a.clone();XRe_shipped_put_k(&mut a,k);XRe_reference_put_k(&mut b,k);assert_eq!(a,b);}
#[kani::proof]
#[kani::unwind(35)]
fn XRe_prepared_selection() {
    let sem=semantic();let mut y1=[0;928];for i in 0..29 {y1[32*i..32*i+32].copy_from_slice(&any_e().to_le_bytes())}
    let point:usize=kani::any();let l:usize=kani::any();kani::assume(point<6&&l<29);
    let actual=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(&y1,l).c0()};
    let expected=if point<3 {sem.claims[point][l]} else if point==3 {sem.extra[l]} else if point==4 {sem.before_z1[l]} else {field(&y1,l).c0()};
    assert_eq!(actual,expected);
}
#[kani::proof]
#[kani::unwind(32)]
fn XRe_prepared_powers29() {let gamma=any_e();let a=powers::<29>(gamma);let mut b=[E::ZERO;29];b[0]=E::ONE;for i in 1..29 {b[i]=b[i-1].mul(gamma)}assert_eq!(a,b);}
#[kani::proof]
#[kani::unwind(10)]
fn XRe_prepared_powers7() {let kappa=any_e();let a=powers::<7>(kappa);let mut b=[E::ZERO;7];b[0]=E::ONE;for i in 1..7 {b[i]=b[i-1].mul(kappa)}assert_eq!(a,b);}
fn check_n<const N:usize>() {let b:[u8;N]=kani::any();let n:usize=kani::any();kani::assume(n<=N);assert_eq!(compact::check_values(&b[..n]),XRe_reference_check_values(&b[..n]));}
#[kani::proof] #[kani::unwind(35)] fn XRe_check_values_y1(){check_n::<464>()}
#[kani::proof] #[kani::unwind(8)] fn XRe_check_values_tail(){check_n::<31>()}
fn expand_n<const N:usize,const O:usize>() {
 let b:[u8;N]=kani::any();let mut a:[u8;O]=kani::any();let mut e=a;
 let n:usize=kani::any();let m:usize=kani::any();kani::assume(n<=N&&m<=O);
 let ar=compact::expand_values(&b[..n],&mut a[..m]);let er=XRe_reference_expand_values(&b[..n],&mut e[..m]);assert_eq!(ar,er);assert_eq!(a,e);
}
#[kani::proof] #[kani::unwind(35)] fn XRe_expand_values_y1(){expand_n::<464,928>()}
#[kani::proof] #[kani::unwind(35)] fn XRe_expand_values_small(){expand_n::<32,64>()}
fn echeck_n<const N:usize>(k:bool) {let b:[u8;N]=kani::any();let n:usize=kani::any();kani::assume(n<=N);assert_eq!(XRe_shipped_echeck(&b[..n],k),XRe_reference_echeck(&b[..n],k));}
#[kani::proof] #[kani::unwind(35)] fn XRe_echeck_y1(){echeck_n::<928>(true)}
#[kani::proof] #[kani::unwind(35)] fn XRe_echeck_wide(){echeck_n::<224>(false)}
#[kani::proof] #[kani::unwind(10)] fn XRe_echeck_tail(){echeck_n::<63>(kani::any())}
#[kani::proof] #[kani::unwind(35)] fn XRe_wide_view() {
 let proof:[u8;compact::PROOF_BYTES]=kani::any();let sem:[u8;13831]=kani::any();let y1:[u8;928]=kani::any();
 let a=XRe_shipped_wide_view(&proof,&sem,&y1);let b=XRe_reference_wide_view(&proof,&sem,&y1);
 match (a,b) {
 (Err(x),Err(y))=>assert_eq!(x,y),
 (Ok(x),Ok(y))=> {assert_eq!(x.variant,y.variant);assert_eq!(x.inactive,y.inactive);assert_eq!(x.semantic.as_ptr(),y.semantic.as_ptr());assert_eq!(x.y1.as_ptr(),y.y1.as_ptr());for (a,b) in [(x.semantic,y.semantic),(x.y1,y.y1),(x.round0,y.round0),(x.round1,y.round1),(x.final_message,y.final_message),(x.query_bytes,y.query_bytes)] {assert_eq!(a.as_ptr(),b.as_ptr());assert_eq!(a.len(),b.len());} assert_eq!(x.folded_root.unwrap().as_ptr(),y.folded_root.unwrap().as_ptr());},
 _=>panic!("result mismatch")
 }
}
