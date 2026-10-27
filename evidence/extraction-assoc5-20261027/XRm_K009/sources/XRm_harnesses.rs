use super::*;
use aspis_core::digest::Digest32;
use aspis_core::circle::SecureCirclePoint;
use aspis_r1_cost_probe::{verifier::{self,candidate,Prepared,Accumulator},transport::Variant};
const P:u32=0x7fff_ffff;
fn canonical(e:E){for x in e.to_limbs(){assert!(x<P);}}
fn k(xs:[u32;4])->K{K{c0:CM31{a:M31(xs[0]),b:M31(xs[1])},c1:CM31{a:M31(xs[2]),b:M31(xs[3])}}}
#[kani::proof] fn XRm_reduce64(){let x:u64=kani::any();let r=M31::reduce_u64(x);assert!(r.0<P);assert_eq!(r.0,(x%(P as u64)) as u32);kani::cover!(x==u64::MAX);}
#[kani::proof] fn XRm_m31_add(){let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P&&b<P);let c=M31(a).add(M31(b));assert!(c.0<P);assert_eq!(c.0,((a as u64+b as u64)%(P as u64))as u32);kani::cover!(a+b>=P);}
#[kani::proof] fn XRm_m31_sub(){let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P&&b<P);let c=M31(a).sub(M31(b));assert!(c.0<P);assert_eq!(c.0,((a as u64+P as u64-b as u64)%(P as u64))as u32);kani::cover!(a<b);}
#[kani::proof] #[kani::unwind(10)] fn XRm_wide_new(){let a:[u32;4]=kani::any();let b:[u32;4]=kani::any();let e=E::new(k(a),k(b));canonical(e);let xs=e.to_limbs();for i in 0..4{assert_eq!(xs[i],a[i]%P);assert_eq!(xs[i+4],b[i]%P);}kani::cover!(a[0]==u32::MAX);}
#[kani::proof] #[kani::unwind(10)] fn XRm_from_limbs(){let xs:[u32;8]=kani::any();if let Some(e)=E::from_limbs(xs){canonical(e);assert_eq!(e.to_limbs(),xs);kani::cover!(xs[7]!=0);}else{assert!(xs.iter().any(|x|*x>=P));}}
#[kani::proof] #[kani::unwind(34)] fn XRm_from_bytes(){let bs:[u8;32]=kani::any();if let Some(e)=E::from_le_bytes(&bs){canonical(e);assert_eq!(e.to_le_bytes(),bs);kani::cover!(bs[31]!=0);}}
#[kani::proof] #[kani::unwind(10)] fn XRm_mul_basis(){let x:u32=kani::any();let y:u32=kani::any();kani::assume(x<P&&y<P);let mut a=[0u32;8];let mut b=[0u32;8];a[0]=x;b[0]=y;let e=E::from_limbs(a).unwrap().mul(E::from_limbs(b).unwrap());canonical(e);assert_eq!(e.to_limbs()[0],((x as u64*y as u64)%(P as u64))as u32);kani::cover!(x>1&&y>1);}
#[kani::proof] #[kani::unwind(10)] fn XRm_powers_two(){let xs:[u32;8]=kani::any();for x in xs{kani::assume(x<P);}let e=E::from_limbs(xs).unwrap();let ps=powers::<2>(e);for i in 0..8{assert_eq!(ps[0].to_limbs()[i],if i==0{1}else{0});assert_eq!(ps[1].to_limbs()[i],xs[i]);}canonical(ps[0]);canonical(ps[1]);kani::cover!(xs[7]!=0);}
#[kani::proof] #[kani::unwind(18)] fn XRm_parse_short(){let bs:[u8;16]=kani::any();assert!(matches!(candidate::parse_shape(&bs),Err(verifier::Error::Parse)));}

// Split after XRl's whole-checkpoint timeout: replace only the zero-valued
// serializers, keeping the actual checkpoint body, heap writes and digests.
fn XRm_zero_wide(e:E)->[u8;32]{assert_eq!(e,E::ZERO);[0;32]}
fn XRm_zero_scalar(x:K,out:&mut[u8]){assert_eq!(x,K::ZERO);assert_eq!(out.len(),16);out.fill(0);}
#[derive(Clone,Copy)] struct Trace<'a>{count:&'a core::cell::Cell<u8>,proof:&'a[u8],public:&'a[u8]}
impl Digest32 for Trace<'_>{fn digest(&self,parts:&[&[u8]])->[u8;32]{let n=self.count.get();self.count.set(n+1);match n{0=>assert_eq!(parts,&[self.proof]),1=>assert_eq!(parts,&[self.public]),2=>{assert_eq!(parts.len(),2);assert_eq!(parts[0],b"UNPROVED:R1:checkpoint");assert_eq!(parts[1].len(),1736);assert_eq!(&parts[1][16..48],&[1u8;32]);assert_eq!(&parts[1][48..80],&[2u8;32]);},_=>panic!("extra digest")};[n+1;32]}}
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(aspis_core::field::WideExact::to_le_bytes,XRm_zero_wide)]
#[kani::stub(aspis_core::field::QM31::write_le_bytes,XRm_zero_scalar)]
fn XRm_checkpoint_digest_split(){
 let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[E::ZERO;2],rho:K::ZERO,queries:[0;22],semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let next:u8=kani::any();let a=Accumulator{weights:alloc::vec![K::ZERO;64],rhs:E::ZERO,power:K::ZERO,next:next as usize};
 let proof:[u8;1]=kani::any();let public:[u8;2]=kani::any();let count=core::cell::Cell::new(0);
 let out=verifier::checkpoint(&p,&a,&proof,&public,Trace{count:&count,proof:&proof,public:&public});
 assert_eq!(count.get(),3);assert_eq!(out.len(),1768);assert_eq!(out[9],next);assert_eq!(&out[1736..],&[3u8;32]);kani::cover!(proof[0]!=public[0]);
}
