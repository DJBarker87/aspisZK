//! Safe owned value references. Recursion exposes bounded control without MIR loop joins.
use aspis_core::r0::{CodeField,domain::Point};
pub fn basis_cell<E:CodeField>(mut out:[E;512],width:usize,j:usize,factor:E)->[E;512] {
    out[width+j]=out[j].mul(factor);out
}
fn basis_fill<E:CodeField>(out:[E;512],width:usize,j:usize,factor:E)->[E;512] {
    if j<width {basis_fill(basis_cell(out,width,j,factor),width,j+1,factor)} else {out}
}
fn basis_round<E:CodeField>(out:[E;512],width:usize,factor:E)->[E;512] {
    if width<512 {
        let out=basis_fill(out,width,0,factor);
        let square=factor.mul(factor);
        basis_round(out,width*2,square.add(square).sub(E::ONE))
    } else {out}
}
pub fn basis<E:CodeField>(x:E)->[E;512] {basis_round([E::ONE;512],1,x)}
fn encoder_fold<E:CodeField>(q:&[E;1024],basis:&[E;512],j:usize,p0:E,p1:E)->(E,E) {
    if j<512 {
        encoder_fold(q,basis,j+1,p0.add(q[2*j].mul(basis[j])),p1.add(q[2*j+1].mul(basis[j])))
    } else {(p0,p1)}
}
pub fn encoder<E:CodeField>(q:&[E;1024],p:Point<E>)->E {
    let basis=basis(p.x);let (p0,p1)=encoder_fold(q,&basis,0,E::ZERO,E::ZERO);
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
fn linears_fold(point:&[QM31;10],variable:usize,suffix:QM31,weighted:QM31)->(QM31,QM31) {
    if variable>0 {
        let variable=variable-1;let suffix=suffix.add(point[variable]);
        let weighted=if variable!=0 {weighted.add(suffix)} else {weighted};
        linears_fold(point,variable,suffix,weighted)
    } else {(suffix,weighted)}
}
fn linears(point:[QM31;10])->(QM31,QM31) {
    let (suffix,weighted)=linears_fold(&point,10,QM31::ZERO,QM31::ZERO);
    (suffix.mul_m31(M31(3)).add(weighted.mul_m31(M31(22))),
     suffix.mul_m31(M31(275)).add(weighted.mul_m31(M31(150))))
}
fn cell(mut out:[QM31;27],index:usize,value:QM31)->[QM31;27] {out[index]=value;out}
fn fill_c1(c1:&[QM31;16],coefficients:[QM31;27],column:usize)->[QM31;27] {
    let exponents:[usize;16]=[0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25];
    if column<16 {
        fill_c1(c1,cell(coefficients,exponents[column],tower(c1[column],column&3)),column+1)
    } else {coefficients}
}
fn fill_mask(mask:&[QM31;10],coefficients:[QM31;27],column:usize)->[QM31;27] {
    let exponents:[usize;10]=[1,3,5,7,9,11,15,17,19,21];
    if column<10 {
        fill_mask(mask,cell(coefficients,exponents[column],tower(mask[column],column&3)),column+1)
    } else {coefficients}
}
fn horner(coefficients:&[QM31;27],prepared:PreparedQm31Multiplier,exponent:usize,shared:QM31)->QM31 {
    if exponent>0 {
        let exponent=exponent-1;
        horner(coefficients,prepared,exponent,prepared.mul(shared).add(coefficients[exponent]))
    } else {shared}
}
pub fn mask(c1:[QM31;16],mask_only:[QM31;10],g:QM31,point:[QM31;10])->QM31 {
    let (linear,explicit_linear)=linears(point);
    let coefficients=fill_c1(&c1,[QM31::ZERO;27],0);
    let coefficients=fill_mask(&mask_only,coefficients,0);
    let prepared=PreparedQm31Multiplier::new(linear);
    let shared=horner(&coefficients,prepared,26,coefficients[26]);
    let x2=explicit_linear.square();let x4=x2.square();let x8=x4.square();let x16=x8.square();
    shared.add(QM31::ONE.add(x16.mul(x8).mul(x2)).mul(g))
}
