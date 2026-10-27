use super::*;
use alloc::vec::Vec;
use aspis_core::{Digest32,circle::SecureCirclePoint};
use aspis_r1_cost_probe::{verifier::{self,Prepared,Accumulator},transport::Variant};
const P:u32=0x7fff_ffff;
fn any_k()->K {let x:[u32;4]=kani::any();K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn limbs(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn any_e()->E {let x:[u32;8]=kani::any();for v in x{kani::assume(v<P);}E::from_limbs(x).unwrap()}
fn partial(x:u64)->u64{(x&(P as u64)).wrapping_add(x>>31)}
fn raw(x:[u32;4],y:[u32;4])->[u64;4]{
 let [a,b,c,d]=x.map(u64::from);let [e,f,g,h]=y.map(u64::from);
 const PP:u64=(P as u64)*(P as u64);
 let u=partial((c*g).wrapping_add(PP).wrapping_sub(d*h));let v=partial((c*h).wrapping_add(d*g));
 [(a*e).wrapping_add(PP).wrapping_sub(b*f).wrapping_add(2*u).wrapping_add(3*u64::from(P)).wrapping_sub(v),
 (a*f).wrapping_add(b*e).wrapping_add(u).wrapping_add(2*v),
 (a*g).wrapping_add(c*e).wrapping_add(2*PP).wrapping_sub(b*h).wrapping_sub(d*f),
 (a*h).wrapping_add(b*g).wrapping_add(c*f).wrapping_add(d*e)]
}
fn reduce(mut x:u64)->u32{x=(x&u64::from(P))+(x>>31);x=(x&u64::from(P))+(x>>31);if x>=u64::from(P){(x-u64::from(P))as u32}else{x as u32}}
struct RefDot{sums:[u64;8],count:usize}
impl RefDot{
 fn new()->Self{Self{sums:[0;8],count:0}}
 fn push(&mut self,x:E,y:K)->Result<(),()>{
  if self.count>=4096{return Err(())}let ys=limbs(y);if ys.iter().any(|v|*v>=P){return Err(())}
  let xs=x.to_limbs();let lo=raw([xs[0],xs[1],xs[2],xs[3]],ys);let hi=raw([xs[4],xs[5],xs[6],xs[7]],ys);
  for j in 0..4{self.sums[j]=self.sums[j].wrapping_add(partial(lo[j]));self.sums[j+4]=self.sums[j+4].wrapping_add(partial(hi[j]));}self.count+=1;Ok(())
 }
 fn finish(self)->E{E::from_limbs(self.sums.map(reduce)).unwrap()}
}
#[kani::proof] #[kani::unwind(10)] fn LPb_dot_one(){let x=any_e();let y=any_k();let mut a=fast_pairing::EbyKDot::new();let mut b=RefDot::new();assert_eq!(a.push(x,y),b.push(x,y));assert_eq!(a.finish(),b.finish());kani::cover!(limbs(y)[3]>=P);kani::cover!(limbs(y)[0]==1);}
#[kani::proof] #[kani::unwind(31)] fn LPb_dot_29(){let xs:[u32;8]=kani::any();for v in xs{kani::assume(v<P)}let x=E::from_limbs(xs).unwrap();let y=any_k();let mut a=fast_pairing::EbyKDot::new();let mut b=RefDot::new();for _ in 0..29{assert_eq!(a.push(x,y),b.push(x,y));}assert_eq!(a.finish(),b.finish());kani::cover!(limbs(y)[0]==1);}
#[kani::proof] #[kani::unwind(10)] fn LPb_powers_seven(){let x=any_e();let a=powers::<7>(x);let mut b=[E::ZERO;7];let mut p=E::ONE;let mut i=0;while i<7{b[i]=p;i+=1;if i<7{p=p.mul(x);}}let at:usize=kani::any();kani::assume(at<7);assert_eq!(a[at],b[at]);kani::cover!(at==6);}
#[derive(Clone,Copy)] struct Trace<'a>{count:&'a core::cell::Cell<u8>,proof:&'a[u8],public:&'a[u8]}
impl Digest32 for Trace<'_>{fn digest(&self,parts:&[&[u8]])->[u8;32]{let n=self.count.get();match n{0=>{assert_eq!(parts.len(),1);assert_eq!(parts[0],self.proof);},1=>{assert_eq!(parts.len(),1);assert_eq!(parts[0],self.public);},2=>{assert_eq!(parts.len(),2);assert_eq!(parts[0],b"UNPROVED:R1:checkpoint");assert_eq!(parts[1].len(),1736);},_=>panic!("extra attempted digest")};self.count.set(n+1);[n+1;32]}}
fn reference_put(out:&mut Vec<u8>,x:E){for b in x.to_le_bytes(){out.push(b)}}
fn reference_k(out:&mut Vec<u8>,x:K){for w in limbs(x){for b in w.to_le_bytes(){out.push(b)}}}
fn reference_checkpoint<H:Digest32>(p:&Prepared,a:&Accumulator,proof:&[u8],public:&[u8],hash:H)->Vec<u8>{
 let mut out=Vec::with_capacity(verifier::checkpoint_size(p.variant));
 for b in b"R1P2CKP2"{out.push(*b)}for b in [p.variant.tag(),a.next as u8,1,0,0,0,0,0]{out.push(b)}
 for b in hash.digest(&[proof]){out.push(b)}for b in hash.digest(&[public]){out.push(b)}for b in p.state{out.push(b)}for r in p.roots{for b in r{out.push(b)}}
 for x in [p.gamma,p.kappa,p.alpha[0],p.alpha[1]]{reference_put(&mut out,x)}reference_k(&mut out,p.rho);
 for q in p.queries{for b in q.to_le_bytes(){out.push(b)}}for x in p.semantic_alpha{reference_k(&mut out,x)}for z in p.z{reference_k(&mut out,z.x);reference_k(&mut out,z.y)}
 for x in [p.claim,a.rhs]{reference_put(&mut out,x)}reference_k(&mut out,a.power);for x in &a.weights{reference_k(&mut out,*x)}for b in hash.digest(&[b"UNPROVED:R1:checkpoint",&out]){out.push(b)}assert_eq!(out.len(),verifier::checkpoint_size(p.variant));out
}
#[kani::proof] #[kani::unwind(70)] fn LPb_checkpoint_full(){
 let e=any_e();let k=any_k();let p=Prepared{variant:Variant::S2,roots:kani::any(),gamma:e,kappa:e,alpha:[e;2],rho:k,queries:kani::any(),semantic_alpha:[k;10],z:[SecureCirclePoint{x:k,y:k};2],claim:e,state:kani::any()};
 let a=Accumulator{weights:alloc::vec![k;64],rhs:e,power:k,next:kani::any()};let proof:[u8;3]=kani::any();let public:[u8;5]=kani::any();let ca=core::cell::Cell::new(0);let cb=core::cell::Cell::new(0);
 let x=verifier::checkpoint(&p,&a,&proof,&public,Trace{count:&ca,proof:&proof,public:&public});let y=reference_checkpoint(&p,&a,&proof,&public,Trace{count:&cb,proof:&proof,public:&public});assert_eq!(ca.get(),3);assert_eq!(cb.get(),3);assert_eq!(x.len(),1768);let at:usize=kani::any();kani::assume(at<1768);assert_eq!(x[at],y[at]);kani::cover!(at==1767);
}
#[kani::proof] #[kani::unwind(18)] fn LPb_scalar_bytes(){let k=any_k();let mut a=[0u8;16];k.write_le_bytes(&mut a);let mut b=Vec::new();reference_k(&mut b,k);let at:usize=kani::any();kani::assume(at<16);assert_eq!(a[at],b[at]);kani::cover!(limbs(k)[3]==u32::MAX);}
#[kani::proof] #[kani::unwind(34)] fn LPb_wide_bytes(){let x=any_e();let a=x.to_le_bytes();let mut b=Vec::new();for w in x.to_limbs(){for v in w.to_le_bytes(){b.push(v)}}let at:usize=kani::any();kani::assume(at<32);assert_eq!(a[at],b[at]);kani::cover!(at==31);}
