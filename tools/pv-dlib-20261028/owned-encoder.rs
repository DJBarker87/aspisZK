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

