use super::{basis,domain::Point,CodeField,Message};
pub fn eval_pair<E: CodeField>(q: &Message<E>, x: E) -> (E, E) {
    let basis = basis::values::<E, 512>(x);
    let mut p0 = E::ZERO;
    let mut p1 = E::ZERO;
    for (pair, n) in q.chunks_exact(2).zip(basis) {
        p0 = p0.add(pair[0].mul(n));
        p1 = p1.add(pair[1].mul(n));
    }
    (p0, p1)
}
pub fn eval_message<E: CodeField>(q: &Message<E>, z: Point<E>) -> E {
    let (p0, p1) = eval_pair(q, z.x);
    p0.add(z.y.mul(p1))
}
