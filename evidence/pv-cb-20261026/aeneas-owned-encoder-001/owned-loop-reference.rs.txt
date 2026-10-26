//! Safe value reference for the current encoder, avoiding iterator state.
use aspis_core::r0::{CodeField,domain::Point};
pub fn basis_cell<E:CodeField>(mut out:[E;512],width:usize,j:usize,factor:E)->[E;512] {
    out[width+j]=out[j].mul(factor);out
}
pub fn basis<E:CodeField>(x:E)->[E;512] {
    let mut out=[E::ONE;512];let mut width=1usize;let mut factor=x;
    while width<512 {
        let mut j=0usize;
        while j<width {out=basis_cell(out,width,j,factor);j+=1;}
        width*=2;
        let square=factor.mul(factor);factor=square.add(square).sub(E::ONE);
    }
    out
}
pub fn encoder<E:CodeField>(q:&[E;1024],p:Point<E>)->E {
    let basis=basis(p.x);let mut p0=E::ZERO;let mut p1=E::ZERO;let mut j=0usize;
    while j<512 {
        p0=p0.add(q[2*j].mul(basis[j]));p1=p1.add(q[2*j+1].mul(basis[j]));j+=1;
    }
    p0.add(p.y.mul(p1))
}

use aspis_core::field::{QM31,CM31,M31,PreparedQm31Multiplier};
fn mul_i(value:CM31)->CM31 {CM31::new(value.b.neg(),value.a)}
fn mul_r(value:CM31)->CM31 {
    CM31::new(value.a.double().sub(value.b),value.a.add(value.b.double()))
}
fn tower(value:QM31,coordinate:usize)->QM31 {
    match coordinate {
        0=>value,
        1=>QM31{c0:mul_i(value.c0),c1:mul_i(value.c1)},
        2=>QM31{c0:mul_r(value.c1),c1:value.c0},
        3=>QM31{c0:mul_i(mul_r(value.c1)),c1:mul_i(value.c0)},
        _=>panic!("invalid tower coordinate"),
    }
}
fn linears(point:[QM31;10])->(QM31,QM31) {
    let mut suffix=QM31::ZERO;let mut weighted=QM31::ZERO;let mut variable=10usize;
    while variable>0 {
        variable-=1;suffix=suffix.add(point[variable]);
        if variable!=0 {weighted=weighted.add(suffix);}
    }
    (suffix.mul_m31(M31(3)).add(weighted.mul_m31(M31(22))),
     suffix.mul_m31(M31(275)).add(weighted.mul_m31(M31(150))))
}
fn cell(mut out:[QM31;27],index:usize,value:QM31)->[QM31;27] {out[index]=value;out}
pub fn mask(c1:[QM31;16],mask_only:[QM31;10],g:QM31,point:[QM31;10])->QM31 {
    let (linear,explicit_linear)=linears(point);
    let mut coefficients=[QM31::ZERO;27];let mut column=0usize;
    let exponents:[usize;16]=[0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25];
    let mask_exponents:[usize;10]=[1,3,5,7,9,11,15,17,19,21];
    while column<16 {coefficients=cell(coefficients,exponents[column],tower(c1[column],column&3));column+=1;}
    column=0;
    while column<10 {coefficients=cell(coefficients,mask_exponents[column],tower(mask_only[column],column&3));column+=1;}
    let prepared=PreparedQm31Multiplier::new(linear);
    let mut shared=coefficients[26];let mut exponent=26usize;
    while exponent>0 {exponent-=1;shared=prepared.mul(shared).add(coefficients[exponent]);}
    let x2=explicit_linear.square();let x4=x2.square();let x8=x4.square();let x16=x8.square();
    shared.add(QM31::ONE.add(x16.mul(x8).mul(x2)).mul(g))
}
