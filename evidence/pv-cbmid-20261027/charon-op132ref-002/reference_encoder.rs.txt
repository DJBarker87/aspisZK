//! Owned indexed P6 candidate. The final unused factor update in values is preserved.
pub fn eval_message_indexed<E:aspis_core::r0::CodeField>(
    q:&[E;1024], z:aspis_core::r0::domain::Point<E>
)->E {
    let basis=crate::r0::basis::values::<E,512>(z.x);
    let mut p0=E::ZERO;
    let mut p1=E::ZERO;
    let mut i=0;
    while i<512 {
        p0=p0.add(q[2*i].mul(basis[i]));
        p1=p1.add(q[2*i+1].mul(basis[i]));
        i+=1;
    }
    p0.add(z.y.mul(p1))
}
