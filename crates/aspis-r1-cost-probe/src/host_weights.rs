//! Prover-local fixed-storage weights (D187 batch 2).
use aspis_core::field::{QM31,QM31 as K,WideExact as E};
use aspis_core::circle::SecureCirclePoint;
use crate::{transport::Variant,verifier::Error};
pub use crate::weights::{QUARTER,PERM};
#[derive(Clone,Copy)]
pub struct Weights {pub variant:Variant,pub factors:[[[K;4];5];5],pub points:[[K;10];3],pub extra:[K;2]}
fn double(x:K)->K { x.mul(x).add(x.mul(x)).sub(K::ONE) }
fn state_only_statement_points(z: &[QM31; 10]) -> [[QM31; 10]; 3] {
    let mut successor = *z;
    let mut carry = QM31::ONE;
    let bit=z[9];let bit_and_carry=bit.mul(carry);successor[9]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[8];let bit_and_carry=bit.mul(carry);successor[8]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[7];let bit_and_carry=bit.mul(carry);successor[7]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[6];let bit_and_carry=bit.mul(carry);successor[6]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[5];let bit_and_carry=bit.mul(carry);successor[5]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[4];let bit_and_carry=bit.mul(carry);successor[4]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[3];let bit_and_carry=bit.mul(carry);successor[3]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[2];let bit_and_carry=bit.mul(carry);successor[2]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[1];let bit_and_carry=bit.mul(carry);successor[1]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[0];let bit_and_carry=bit.mul(carry);successor[0]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let mut absorption = *z;
    absorption[7] = QM31::ONE.sub(absorption[7]);
    absorption[6] = QM31::ONE.sub(absorption[6]);
    [*z, successor, absorption]
}

impl Weights {
#[inline(never)]
pub fn new(variant:Variant,alpha:&[K;10],z:&[SecureCirclePoint;2])->Result<Weights,Error> {
        let points=state_only_statement_points(alpha);
        let extra=[alpha[8],alpha[9]];
        let mut factors=[[[K::ZERO;4];5];5];
    let a=points[0][3];let b=points[0][2];factors[0][0]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[0][1];let b=points[0][0];factors[0][1]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[0][5];let b=points[0][4];factors[0][2]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[0][9];let b=points[0][8];factors[0][3]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[0][7];let b=points[0][6];factors[0][4]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[1][3];let b=points[1][2];factors[1][0]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[1][1];let b=points[1][0];factors[1][1]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[1][5];let b=points[1][4];factors[1][2]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[1][9];let b=points[1][8];factors[1][3]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[1][7];let b=points[1][6];factors[1][4]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[2][3];let b=points[2][2];factors[2][0]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[2][1];let b=points[2][0];factors[2][1]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[2][5];let b=points[2][4];factors[2][2]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[2][9];let b=points[2][8];factors[2][3]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[2][7];let b=points[2][6];factors[2][4]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    factors[3][0]=[K::ONE,z[0].y,z[0].x,z[0].x.mul(z[0].y)];let mut x=double(z[0].x);
    let y=double(x);factors[3][1]=[K::ONE,x,y,x.mul(y)];x=double(y);
    let y=double(x);factors[3][2]=[K::ONE,x,y,x.mul(y)];x=double(y);
    let y=double(x);factors[3][3]=[K::ONE,x,y,x.mul(y)];x=double(y);
    let y=double(x);factors[3][4]=[K::ONE,x,y,x.mul(y)];x=double(y);
    factors[4][0]=[K::ONE,z[1].y,z[1].x,z[1].x.mul(z[1].y)];let mut x=double(z[1].x);
    let y=double(x);factors[4][1]=[K::ONE,x,y,x.mul(y)];x=double(y);
    let y=double(x);factors[4][2]=[K::ONE,x,y,x.mul(y)];x=double(y);
    let y=double(x);factors[4][3]=[K::ONE,x,y,x.mul(y)];x=double(y);
    let y=double(x);factors[4][4]=[K::ONE,x,y,x.mul(y)];x=double(y);
        Ok(Weights {variant,factors,points,extra})
}
    pub fn raw(&self,kind:usize,j:usize)->K { raw_value(*self,kind,j) }

    /// The caller owns allocation and retains Error::Allocation before this kernel.
    pub fn materialize(&self,kappa:E,w:&mut [E;1024])->Result<(),Error> {
        let out=materialize_values(*self,kappa,*w);
        *w=out;
        Ok(())
    }
}

// The loop carries owned fixed arrays, with no loan from the caller at its joins.
fn materialize_values(weights:Weights,kappa:E,mut out:[E;1024])->[E;1024] {
        let kp=crate::prover_powers::powers::<7>(kappa);
        let k0=kp[0]; let k1=kp[1]; let k2=kp[2]; let k3=kp[3];
        let k4=kp[4]; let k5=kp[5]; let k6=kp[6];
        let mut j=0usize;
        while j<1024 {
            let mut v=E::ZERO;
            v=v.add(mul_qm31(k0,raw_value(weights,0,j)));
            v=v.add(mul_qm31(k1,raw_value(weights,1,j)));
            v=v.add(mul_qm31(k2,raw_value(weights,2,j)));
            v=v.add(mul_qm31(k3,raw_value(weights,3,j)));
            v=v.add(mul_qm31(k4,raw_value(weights,4,j)));
            v=v.add(mul_qm31(k5,raw_value(weights,5,j)));
            v=v.add(mul_qm31(k6,raw_value(weights,6,j)));
            out[j]=v; j+=1;
        }
        out
}
fn raw_value(weights:Weights,kind:usize,j:usize)->K {
        if kind==0 {
            let r=weights.variant.row(j);
            return if (aspis_core::r0::opening::COPY_ACTIVE_ROW_MASKS[r/16]>>(r%16))&1==0 {K::ONE}else{K::ZERO};
        }
        if kind==4 {
            if j<56 { return weights.extra[j/28].pow((j%28) as u64); }
            return K::ZERO;
        }
        if kind>=1 && kind<=3 && weights.variant==Variant::D {
            let r=weights.variant.row(j);
            return point_raw(weights.points[kind-1],r);
        }
        let k=if kind<4 {kind-1}else{kind-2};
        tensor_raw(weights.factors[k],j)
}

// Copy values before branch joins: no mutable element loan or restoration.
fn point_factor(point:K,r:usize,b:u32)->K {
    if r&(1usize<<b)==0 {K::ONE.sub(point)}else{point}
}
fn point_raw(points:[K;10],r:usize)->K {
    let mut v=K::ONE;
    v=v.mul(point_factor(points[9],r,0));
    v=v.mul(point_factor(points[8],r,1));
    v=v.mul(point_factor(points[7],r,2));
    v=v.mul(point_factor(points[6],r,3));
    v=v.mul(point_factor(points[5],r,4));
    v=v.mul(point_factor(points[4],r,5));
    v=v.mul(point_factor(points[3],r,6));
    v=v.mul(point_factor(points[2],r,7));
    v=v.mul(point_factor(points[1],r,8));
    v=v.mul(point_factor(points[0],r,9));
    v
}
fn tensor_raw(factors:[[K;4];5],j:usize)->K {
    let mut v=K::ONE;
    v=v.mul(factors[0][(j>>0u32)&3]);
    v=v.mul(factors[1][(j>>2u32)&3]);
    v=v.mul(factors[2][(j>>4u32)&3]);
    v=v.mul(factors[3][(j>>6u32)&3]);
    v=v.mul(factors[4][(j>>8u32)&3]);
    v
}
// Avoid canonical_qm31's FnOnce closure Drop in the extraction closure.
// The four reductions are exactly the shipped canonicalization of raw K.
fn mul_qm31(x:E,rhs:K)->E {
    use aspis_core::field::{CM31,M31,ct};
    let rhs=K {
        c0:CM31 {a:M31(ct::reduce64(rhs.c0.a.0 as u64)),b:M31(ct::reduce64(rhs.c0.b.0 as u64))},
        c1:CM31 {a:M31(ct::reduce64(rhs.c1.a.0 as u64)),b:M31(ct::reduce64(rhs.c1.b.0 as u64))},
    };
    let a=x.c0().mul(rhs);
    let b=x.c1().mul(rhs);
    E::from_limbs([a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0,
                   b.c0.a.0,b.c0.b.0,b.c1.a.0,b.c1.b.0]).unwrap()
}
