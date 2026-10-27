use aspis_core::field::QM31;
use aspis_core::field::QM31 as K;
use aspis_core::circle::SecureCirclePoint;
#[derive(Clone,Copy)] pub enum Variant { S1,S2,D }
#[derive(Clone,Copy)] pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }
const TAU:[usize;5]=[3,4,2,0,1];
#[derive(Clone,Copy)] pub struct Weights {pub variant:Variant,pub factors:[[[K;4];5];5],pub points:[[K;10];3],pub extra:[K;2]}
fn double(x:K)->K { x.mul(x).add(x.mul(x)).sub(K::ONE) }
fn state_only_statement_points(z: &[QM31; 10]) -> [[QM31; 10]; 3] {
    let mut successor = *z;
    let mut carry = QM31::ONE;
    let mut coordinate=10usize; while coordinate>0 { coordinate-=1;
        let bit = z[coordinate];
        let bit_and_carry = bit.mul(carry);
        successor[coordinate] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
    }
    let mut absorption = *z;
    absorption[7] = QM31::ONE.sub(absorption[7]);
    absorption[6] = QM31::ONE.sub(absorption[6]);
    [*z, successor, absorption]
}

pub fn weights_new(variant:Variant,alpha:&[K;10],z:&[SecureCirclePoint;2])->Result<Weights,Error> {
        let points=state_only_statement_points(alpha);
        let extra=[alpha[8],alpha[9]];
        let mut factors=[[[K::ZERO;4];5];5];
        let mut k=0usize; while k<3 { let mut d=0usize; while d<5 {
            let a=points[k][9-2*TAU[d]]; let b=points[k][8-2*TAU[d]];
            factors[k][d]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
        d+=1;} k+=1;}
        let mut k=0usize; while k<2 {
            factors[3+k][0]=[K::ONE,z[k].y,z[k].x,z[k].x.mul(z[k].y)];
            let mut x=double(z[k].x);
            let mut d=1usize; while d<5 {
                let y=double(x); factors[3+k][d]=[K::ONE,x,y,x.mul(y)]; x=double(y);d+=1;
            }
        k+=1;}
        Ok(Weights {variant,factors,points,extra})
}
