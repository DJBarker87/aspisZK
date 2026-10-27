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

pub fn weights_new(variant:Variant,alpha:&[K;10],z:&[SecureCirclePoint;2])->Result<Weights,Error> {
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
