//! Beta is absorbed into all 29 coefficients ONCE per proof.
//! The source adapter must retain the current mixed-width C1 dot backend.
use crate::canonical::{Q,P};
#[derive(Debug,Clone,Copy,PartialEq,Eq)]pub enum Error{Length,Canonical}
pub struct BetaPowers {pub base:[Q;26],pub helpers:[Q;3]}
impl BetaPowers {
    pub fn new(original:&[Q;29],beta:Q)->Self{
        let left=Q::ONE.sub(beta);
        Self{base:core::array::from_fn(|i|left.mul(original[i])),
            helpers:[left.mul(original[26]),beta.mul(original[27]),left.mul(original[28])]}
    }
}
fn decode<const N:usize>(bytes:&[u8],out:&mut[u32;N])->Result<(),Error>{
    if N==0||N%8!=0||bytes.len()!=N/8*31{return Err(Error::Length)}
    let mut invalid=false;
    for (block,b) in bytes.chunks_exact(31).enumerate(){
        let load=|j:usize|u64::from_le_bytes(b[j..j+8].try_into().unwrap());
        let (w0,w1,w2,w3)=(load(0),load(8),load(16),load(23)>>8);
        let v=[w0,w0>>31,(w0>>62)|(w1<<2),w1>>29,(w1>>60)|(w2<<4),w2>>27,(w2>>58)|(w3<<6),w3>>25];
        for j in 0..8{let x=(v[j]&u64::from(P)) as u32;out[8*block+j]=x;invalid|=x==P;}
    }
    if invalid{Err(Error::Canonical)}else{Ok(())}
}
/// Portable reference-shaped implementation. Replace the scalar C1 summation
/// with the RETAINED partial-reduction mixed-width dot when source integrating.
/// Do not replace efficient source C1 dots with full-QM31 multiplication.
pub fn combine(c1:&[u8],c2:&[u8],p:&BetaPowers)->Result<[Q;4],Error>{
    let mut a=[0u32;104];let mut b=[0u32;48];decode(c1,&mut a)?;decode(c2,&mut b)?;
    // Both complete inputs have been checked, even at beta=0 or beta=1.
    Ok(core::array::from_fn(|slot|{
        let mut sum=Q::ZERO;for col in 0..26{sum=sum.add(p.base[col].mul_m31(a[26*slot+col]).unwrap());}
        let mut helpers=crate::whole_dot::Dot::new();
        for h in 0..3{let j=4*(4*h+slot);let q=Q::from_limbs([b[j],b[j+1],b[j+2],b[j+3]]).unwrap();helpers.push(p.helpers[h],q).unwrap();}
        sum.add(helpers.finish())
    }))
}
