//! Fold weights times the conjugate chord, before CM31 norm inversion.
//! Only the source-selected unit-circle points and their SAME line values apply.
use super::*;
fn conjugate(v:K)->K {K{c0:v.c0,c1:v.c1.neg()}}
struct Prepared {even:K,x:[K;2],y:[K;2],cross:[K;2]}
impl Prepared {
    fn new(abc:[K;3],alpha:K)->Self {
        let [a,b,c]=abc.map(conjugate);
        let a2=alpha.square();let a3=a2.mul(alpha);
        let ca2=c.mul(a2);
        Self {even:a.add(b.mul(a2)).add(c.mul(alpha)).half().half(),
            x:[a.mul(a2).add(c.mul(a3)),b],
            y:[a.mul(alpha).add(b.mul(a3)),c],
            cross:[a.mul(a3).add(ca2),b.mul(alpha).sub(ca2)]}
    }
    fn four(&self,x:M31,y:M31,ix:M31,iy:M31)->[K;4] {
        // ix=1/(2x), iy=1/(2y). Use x^2+y^2=1 exactly, never a hint.
        let cx=self.x[0].mul_m31(ix.half()).add(self.x[1].mul_m31(x.half().half()));
        let cy=self.y[0].mul_m31(iy.half()).add(self.y[1].mul_m31(y.half().half()));
        let cross=self.cross[0].mul_m31(ix.mul(iy))
            .add(self.cross[1].mul_m31(x.mul(iy).half()));
        let positive=self.even.add(cx);let negative=self.even.sub(cx);
        let plus=cy.add(cross);let minus=cy.sub(cross);
        [positive.add(plus),positive.sub(plus),negative.sub(minus),negative.add(minus)]
    }
}
pub(super) fn inverse(selected:&Selected,values:&[K],abc:[K;3],base:&[M31],lines:&[M31],alpha:K)->Result<Vec<K>,Error>{
    let (norms,base_inv)=super::norm_inverse(selected,values,abc,base,lines)?;
    let coeff=Prepared::new(abc,alpha);
    let mut out=Vec::with_capacity(values.len());
    for (i,p) in selected.points().iter().enumerate() {
        let weights=coeff.four(p.x,p.y,base_inv[2*i],base_inv[2*i+1]);
        for (j,v) in weights.into_iter().enumerate() {
            let ni=norms[4*i+j];out.push(K{c0:v.c0.mul(ni),c1:v.c1.mul(ni)});
        }
    }
    Ok(out)
}
