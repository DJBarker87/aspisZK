//! SPEC §§3–4: direct evaluators of natural-coefficient messages.

use super::{
    basis,
    domain::{self, FibreIndex, InitialIndex, Point},
    CodeField, FinalMessage, Message,
};

/// SPEC §3: evaluations of (p0_q,p1_q) at x in O(512) field operations.
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
pub fn p0_q<E: CodeField>(q: &Message<E>, x: E) -> E {
    eval_pair(q, x).0
}
pub fn p1_q<E: CodeField>(q: &Message<E>, x: E) -> E {
    eval_pair(q, x).1
}

/// SPEC §3: evalMessage(q,(x,y))=p0_q(x)+y*p1_q(x), including OOD.
pub fn eval_message<E: CodeField>(q: &Message<E>, z: Point<E>) -> E {
    let (p0, p1) = eval_pair(q, z.x);
    p0.add(z.y.mul(p1))
}
/// SPEC §3: Enc(q)[i]; a word is represented by its pointwise evaluator.
pub fn exact_initial_encoder<E: CodeField>(q: &Message<E>, i: InitialIndex) -> E {
    eval_message(q, domain::stored_point(i))
}
/// SPEC §4: Σ_d F[d]*N_d(line_node(u)), with 256 natural coefficients.
pub fn exact_final_encoder<E: CodeField>(q: &FinalMessage<E>, u: FibreIndex) -> E {
    q.iter()
        .zip(basis::values::<E, 256>(domain::line_node(u)))
        .fold(E::ZERO, |sum, (&coefficient, n)| {
            sum.add(coefficient.mul(n))
        })
}
