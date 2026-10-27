use aspis_core::r0::{CodeField,Message,domain::Point};
fn values<E:CodeField,const N:usize>(x:E)->[E;N] {
    let mut out=[E::ONE;N];let mut width=1usize;let mut factor=x;
    while width<N {
        let limit=width.min(N-width);let mut j=0usize;
        while j<limit {out[width+j]=out[j].mul(factor);j+=1;}
        width*=2;let square=factor.mul(factor);factor=square.add(square).sub(E::ONE);
    }
    out
}
fn eval_pair<E:CodeField>(q:Message<E>,x:E)->(E,E) {
    let basis=values::<E,512>(x);let mut p0=E::ZERO;let mut p1=E::ZERO;
    let mut i=0usize;
    while i<512 {let n=basis[i];p0=p0.add(q[2*i].mul(n));p1=p1.add(q[2*i+1].mul(n));i+=1;}
    (p0,p1)
}
pub fn eval_message<E:CodeField>(q:&Message<E>,z:Point<E>)->E {
    let (p0,p1)=eval_pair(*q,z.x);p0.add(z.y.mul(p1))
}
