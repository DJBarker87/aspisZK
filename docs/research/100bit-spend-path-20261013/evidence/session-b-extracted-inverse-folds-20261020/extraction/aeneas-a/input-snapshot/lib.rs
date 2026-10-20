// Exact frozen fold helper bodies; field arithmetic is an explicit opaque boundary.
pub mod aspis_core { pub mod field {
#[derive(Clone,Copy)] pub struct M31(pub u32);
#[derive(Clone,Copy)] pub struct CM31 { pub a:M31,pub b:M31 }
#[derive(Clone,Copy)] pub struct QM31 { pub c0:CM31,pub c1:CM31 }
#[derive(Clone,Copy)] pub struct WideExact { c0:QM31,c1:QM31 }
impl M31 { pub fn mul(self,_:Self)->Self {unreachable!()} }
impl WideExact {
 pub fn add(self,_:Self)->Self {unreachable!()}
 pub fn sub(self,_:Self)->Self {unreachable!()}
 pub fn mul(self,_:Self)->Self {unreachable!()}
 pub fn mul_m31(self,_:M31)->Self {unreachable!()}
}
}}
pub mod weights { use crate::aspis_core::field::M31; pub const QUARTER:M31=M31(536870912); }
pub mod verifier { use crate::aspis_core::field::{WideExact as E,M31}; use crate::weights::QUARTER;
fn circle_fold_with_inverses(alpha:E,a:[E;4],inverse:&[M31;5])->E {
    let [ix,iy,_,_,_]=*inverse;let [a,b,c,d]=a;
    let h0=a.add(b).add(c).add(d).mul_m31(QUARTER);
    let h1=a.sub(b).sub(c).add(d).mul_m31(QUARTER.mul(iy));
    let h2=a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(ix));
    let h3=a.sub(b).add(c).sub(d).mul_m31(QUARTER.mul(ix).mul(iy));
    h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
}

fn line_fold_with_inverses(alpha:E,a:[E;4],inverse:&[M31;5])->E {
    let [_,_,ix,iy,iz]=*inverse;let half=M31(1073741824);let [a,b,c,d]=a;
    let h0=a.add(b).add(c).add(d).mul_m31(QUARTER);
    let h2=a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(iz));
    let c0=a.sub(b).mul_m31(half.mul(ix));
    let c1=d.sub(c).mul_m31(half.mul(iy));
    let h1=c0.add(c1).mul_m31(half);
    let h3=c0.sub(c1).mul_m31(half.mul(iz));
    h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
}
}
