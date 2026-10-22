#![allow(dead_code,unused_imports,unused_variables,non_snake_case)]
extern crate self as aspis_core;
use alloc::vec::Vec;
extern crate alloc;
pub mod field {
 #[derive(Clone,Copy,Debug,Default,PartialEq,Eq)] pub struct M31(pub u32);
 #[derive(Clone,Copy,Debug,Default,PartialEq,Eq)] pub struct CM31 {pub a:M31,pub b:M31}
 #[derive(Clone,Copy,Debug,Default,PartialEq,Eq)] pub struct QM31 {pub c0:CM31,pub c1:CM31}
 #[derive(Clone,Copy,Debug,Default,PartialEq,Eq)] pub struct WideExact {pub c0:QM31,pub c1:QM31}
 impl M31 {pub const ZERO:Self=Self(0);pub fn mul(self,_r:Self)->Self{unreachable!()}}
 impl QM31 {pub const ZERO:Self=Self{c0:CM31{a:M31(0),b:M31(0)},c1:CM31{a:M31(0),b:M31(0)}};pub const ONE:Self=Self{c0:CM31{a:M31(1),b:M31(0)},c1:CM31{a:M31(0),b:M31(0)}}; pub fn mul(self,_r:Self)->Self{unreachable!()} pub fn pow(self,_n:u64)->Self{unreachable!()} pub fn square(self)->Self{unreachable!()} }
 impl WideExact {pub const ZERO:Self=Self{c0:QM31::ZERO,c1:QM31::ZERO};pub const ONE:Self=Self{c0:QM31::ONE,c1:QM31::ZERO};pub fn add(self,_r:Self)->Self{unreachable!()}pub fn mul(self,_r:Self)->Self{unreachable!()}pub fn sub(self,_r:Self)->Self{unreachable!()}pub fn mul_m31(self,_r:M31)->Self{unreachable!()}pub fn mul_qm31(self,_r:QM31)->Self{unreachable!()} pub fn from_le_bytes(_bytes:&[u8])->Option<Self>{unreachable!()} }
}
pub mod transport {#[derive(Clone,Copy,Debug,PartialEq,Eq)]pub enum Variant{S1,S2,D}}
pub mod verifier {#[derive(Clone,Copy,Debug,PartialEq,Eq)]pub enum Error{Parse,Allocation}}
pub mod fast_pairing {
 use crate::field::{WideExact,QM31};
 pub mod canonical {
  #[derive(Clone,Copy,Debug,Default,PartialEq,Eq)]
  pub struct Dot { pub sums:[u64;4] }
 }
 #[derive(Clone,Copy,Debug,Default,PartialEq,Eq)]
 pub struct EbyKDot { pub c0:canonical::Dot, pub c1:canonical::Dot, pub count:usize }
 impl EbyKDot {
  pub fn new()->Self { Self {c0:canonical::Dot{sums:[0;4]}, c1:canonical::Dot{sums:[0;4]}, count:0} }
  pub fn push(&mut self,_a:WideExact,_b:QM31)->Result<(),()>{unreachable!()}
  pub fn finish(self)->WideExact{unreachable!()}
 }
}
pub mod r0 {pub mod heap {use alloc::vec::Vec;use crate::verifier::Error;pub fn filled<T:Copy>(n:usize,v:T)->Result<Vec<T>,Error>{Ok(alloc::vec![v;n])}}}
#[path="trace.rs"] pub mod trace;
pub mod weights {
 use alloc::vec::Vec;use crate::{field::{QM31 as K,WideExact as E,M31},transport::Variant,verifier::Error};
 const QUARTER:M31=M31(536870912);const PERM:[usize;4]=[0,3,2,1];
 pub fn powers<const N:usize>(_x:E)->[E;N]{unreachable!()} pub fn kpowers<const N:usize>(_x:K)->[K;N]{unreachable!()} pub fn field(bytes:&[u8],i:usize)->E { E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap() }
 pub fn grouped_inactive_pair(_w:&Weights,_f:&[u8],_low:&[E;16])->E{unreachable!()} pub fn twofold_libra_weights(_low:&[E;16],_extra:[K;2])->[E;4]{unreachable!()} pub fn factored_s2_libra_weights(_a:&[E;4],_b:&[E;4],_extra:[K;2])->[E;4]{unreachable!()}
 // Candidate normalization: isolate each fallible inner scan so its `?` is
 // in a single Rust loop frame; retain every Result/error branch.
 fn push_byte_products(pair:&mut crate::fast_pairing::EbyKDot,f:&[u8],scratch:&[K],n:usize)->Result<(),Error>{
  for j in 0..n { pair.push(field(f,j),scratch[j]).map_err(|_|Error::Parse)?; }
  Ok(())
 }
 fn partial_dot(f:&[u8],common:&[K;16],s:usize)->Result<E,Error>{
  let mut dot=crate::fast_pairing::EbyKDot::new();
  for j in 0..16 { dot.push(field(f,16*s+j),common[j]).map_err(|_|Error::Parse)?; }
  Ok(dot.finish())
 }
 fn high_dot(partials:&[E;4],coeffs:&[K;4])->Result<E,Error>{
  let mut high=crate::fast_pairing::EbyKDot::new();
  for s in 0..4 { high.push(partials[s],coeffs[s]).map_err(|_|Error::Parse)?; }
  Ok(high.finish())
 }
 fn eq_k(a:K,b:K)->bool{
  if a.c0.a.0==b.c0.a.0 { if a.c0.b.0==b.c0.b.0 {
   if a.c1.a.0==b.c1.a.0 { a.c1.b.0==b.c1.b.0 } else { false }
  } else { false } } else { false }
 }
 fn eq4(a:&[K;4],b:&[K;4])->bool{
  if eq_k(a[0],b[0]) { if eq_k(a[1],b[1]) {
   if eq_k(a[2],b[2]) { eq_k(a[3],b[3]) } else { false }
  } else { false } } else { false }
 }
 fn is_shared_two_point(w:&Weights,folds:usize)->bool{
  if w.variant==Variant::S2 { if folds==2 {
   if eq4(&w.factors[0][2],&w.factors[2][2]) { eq4(&w.factors[0][3],&w.factors[2][3]) } else { false }
  } else { false } } else { false }
 }
 fn libra_for(w:&Weights,low:&[E;16],ap0:&[E;4],ap1:&[E;4])->[E;4]{
  if w.variant==Variant::S2 { factored_s2_libra_weights(ap0,ap1,w.extra) }
  else { twofold_libra_weights(low,w.extra) }
 }
 fn onefold_extra_pair(f:&[u8],p:&[K;5],side:usize)->E{
  let mut power=K::ONE; let mut pair=E::ZERO;
  for j in 0..7 { pair=pair.add(field(f,j+7*side).mul_qm31(power)); power=power.mul(p[4]); }
  pair
 }
 fn prepare_standard_rows(w:&Weights,alpha:&[E],f:&[u8],folds:usize,n:usize,
     ap0:&[E;4],ap1:&[E;4],scratch:&mut Vec<K>,parts:&mut [E;7],shared:bool)->Result<(),Error>{
  // Preserve the original left-to-right call and first-error order.
  if !shared { process_kind(w,1,alpha,f,folds,n,ap0,ap1,scratch,parts)?; }
  process_kind(w,2,alpha,f,folds,n,ap0,ap1,scratch,parts)?;
  if !shared { process_kind(w,3,alpha,f,folds,n,ap0,ap1,scratch,parts)?; }
  process_kind(w,5,alpha,f,folds,n,ap0,ap1,scratch,parts)?;
  process_kind(w,6,alpha,f,folds,n,ap0,ap1,scratch,parts)?;
  Ok(())
 }
 fn prepare_shared_rows(w:&Weights,f:&[u8],ap0:&[E;4],ap1:&[E;4],parts:&mut [E;7])->Result<(),Error>{
  // Keep each partial/high dot in its original order so the first error is unchanged.
  let common:[K;16]=core::array::from_fn(|j|
      w.factors[0][2][j&3].mul(w.factors[0][3][j>>2]));
  let mut partials=[E::ZERO;4];
  partials[0]=partial_dot(f,&common,0)?;
  partials[1]=partial_dot(f,&common,1)?;
  partials[2]=partial_dot(f,&common,2)?;
  partials[3]=partial_dot(f,&common,3)?;
  let high0=high_dot(&partials,&w.factors[0][4])?;
  let scale0=Weights::scalar_factor(&w.factors[0][0],ap0)
      .mul(Weights::scalar_factor(&w.factors[0][1],ap1));
  parts[1]=scale0.mul(high0);
  let high2=high_dot(&partials,&w.factors[2][4])?;
  let scale2=Weights::scalar_factor(&w.factors[2][0],ap0)
      .mul(Weights::scalar_factor(&w.factors[2][1],ap1));
  parts[3]=scale2.mul(high2);
  Ok(())
 }
 pub struct Weights {pub variant:Variant,pub factors:[[[K;4];5];5],pub points:[[K;10];3],pub extra:[K;2]}

 // Candidate normalization: one source row's fallible work is isolated from
 // its caller so the caller can preserve first-error order without a loop.
 fn process_kind(w:&Weights,kind:usize,alpha:&[E],f:&[u8],folds:usize,n:usize,
     ap0:&[E;4],ap1:&[E;4],scratch:&mut Vec<K>,parts:&mut [E;7])->Result<(),Error>{
  if w.variant==Variant::D && kind<4 {
   parts[kind]=w.dense_point_pair(kind,alpha,f)?;
  } else {
   let k=if kind<4 {kind-1}else{kind-2};
   w.tensor(k,folds,scratch);
   let mut scale=Weights::scalar_factor(&w.factors[k][0],ap0);
   if folds==2 {scale=scale.mul(Weights::scalar_factor(&w.factors[k][1],ap1));}
   let mut pair=crate::fast_pairing::EbyKDot::new();
   push_byte_products(&mut pair,f,scratch,n)?;
   parts[kind]=scale.mul(pair.finish());
  }
  Ok(())
 }
 impl Weights {pub fn raw(&self,_kind:usize,_j:usize)->K{unreachable!()}pub fn tensor(&self,_k:usize,_folds:usize,_out:&mut[K]){unreachable!()}pub fn scalar_factor(_f:&[K;4],_p:&[E;4])->E{unreachable!()}pub fn dense_point_pair(&self,_kind:usize,_alpha:&[E],_f:&[u8])->Result<E,Error>{unreachable!()}
    #[inline(never)]
    pub fn pair(&self,alpha:&[E],f:&[u8],kappa:E)->Result<E,Error> {
        let n=f.len()/32; let folds=alpha.len();
        if n!=1024>>(2*folds) {return Err(Error::Parse);}
        let ap0=powers::<4>(alpha[0]);
        let ap1=if folds==2 {powers::<4>(alpha[1])}else{[E::ONE;4]};
        let mut scratch=aspis_core::r0::heap::filled(n,K::ZERO).map_err(|_|Error::Allocation)?;
        let mut parts=[E::ZERO;7];
        // On S2's two-fold path the high tensor factors for point rows 0 and
        // 2 are identical. Keep the equality guard so arbitrary constructed
        // `Weights` values retain the original per-row fallback.
        let shared_two_point = is_shared_two_point(self,folds);
        prepare_standard_rows(self,alpha,f,folds,n,&ap0,&ap1,&mut scratch,&mut parts,shared_two_point)?;
        if shared_two_point { prepare_shared_rows(self,f,&ap0,&ap1,&mut parts)?; }
        if folds==1 {
            let dual:[E;16]=core::array::from_fn(|mask|(0..4).filter(|&s|mask&(1<<s)!=0).fold(E::ZERO,|v,s|v.add(ap0[PERM[s]])).mul_m31(QUARTER));
            let mut groups=[E::ZERO;16];
            for j in 0..n {
                let mut mask=0;
                for s in 0..4 {if self.raw(0,4*j+s)==K::ONE {mask|=1<<s;}}
                groups[mask]=groups[mask].add(field(f,j));
            }
            for m in 1..16 {parts[0]=parts[0].add(groups[m].mul(dual[m]));}
            for side in 0..2 {
                let p=kpowers::<5>(self.extra[side]);
                let scale=Self::scalar_factor(&[p[0],p[1],p[2],p[3]],&ap0);
                let pair=onefold_extra_pair(f,&p,side);
                parts[4]=parts[4].add(pair.mul(scale));
            }
        } else {
            // Two-fold 0/1 row: compute the sixteen challenge products once.
            // Coefficients with the same inactive mask share one subset sum.
            let low:[E;16]=core::array::from_fn(|s|ap0[PERM[s%4]].mul(ap1[PERM[s/4]]).mul_m31(QUARTER.mul(QUARTER)));
            parts[0]=grouped_inactive_pair(self,f,&low);
            let libra=libra_for(self,&low,&ap0,&ap1);
            for j in 0..4 {parts[4]=parts[4].add(field(f,j).mul(libra[j]));}
        }
        #[cfg(feature="prover")]
        for kind in 0..7 {
            for j in 0..1024 {crate::trace::value(6,kind*1024+j,E::from_qm31(self.raw(kind,j)));}
            for j in 0..n {crate::trace::value(7,kind*n+j,self.dual_raw(kind,j,alpha));}
        }
        let k=powers::<7>(kappa);let mut sum=E::ZERO;
        for kind in 0..7 {crate::trace::value(8,kind,parts[kind]);sum=sum.add(k[kind].mul(parts[kind]));}
        Ok(sum)
    }
 }
 // Extraction-only root shim: Charon cannot use an inherent method as --start-from.
 pub fn pair_root(w:&Weights,alpha:&[E],f:&[u8],kappa:E)->Result<E,Error>{
  w.pair(alpha,f,kappa)
 }

}
