//! SPEC §4: four-point transform, folds, and the separate quarter.

use super::{
    domain::{self, FibreIndex, InitialIndex, SlotIndex},
    CodeField, Error, FinalMessage, Message,
};
use crate::field::M31;

/// SPEC §4: inverse(4)=536870912, embedded from F. Not part of dual_fold.
pub fn quarter<E: CodeField>() -> E {
    E::from_m31(M31(536870912))
}

/// SPEC §4: φ(a) with explicit denominator failures, in channel order 0..3.
pub fn phi<E: CodeField>(x: E, y: E, a: [E; 4]) -> Result<[E; 4], Error> {
    let inv_x = x.try_inv().ok_or(Error::ZeroDenominator)?;
    let inv_y = y.try_inv().ok_or(Error::ZeroDenominator)?;
    let q = quarter::<E>();
    let [a0, a1, a2, a3] = a;
    Ok([
        a0.add(a1).add(a2).add(a3).mul(q),
        a0.sub(a1).sub(a2).add(a3).mul(q).mul(inv_y),
        a0.add(a1).sub(a2).sub(a3).mul(q).mul(inv_x),
        a0.sub(a1).add(a2).sub(a3).mul(q).mul(inv_x).mul(inv_y),
    ])
}
/// SPEC §4: inverse φ (fibreEvaluate), without divisions.
pub fn phi_inverse<E: CodeField>(x: E, y: E, h: [E; 4]) -> [E; 4] {
    let [h0, h1, h2, h3] = h;
    let a = y.mul(h1);
    let b = x.mul(h2);
    let c = x.mul(y).mul(h3);
    [
        h0.add(a).add(b).add(c),
        h0.sub(a).add(b).sub(c),
        h0.sub(a).sub(b).add(c),
        h0.add(a).sub(b).sub(c),
    ]
}
fn combine<E: CodeField>(alpha: E, h: [E; 4]) -> E {
    h[0].add(alpha.mul(h[1].add(alpha.mul(h[2].add(alpha.mul(h[3]))))))
}
/// SPEC §4: foldWord at one fibre, given its four consecutive values.
pub fn fold_fibre<E: CodeField>(alpha: E, u: FibreIndex, a: [E; 4]) -> Result<E, Error> {
    let point = domain::fibre_point(u);
    Ok(combine(alpha, phi(point.x, point.y, a)?))
}
/// SPEC §4: foldWord(α,word)[u] for a function-backed full word.
pub fn fold_word<E: CodeField>(
    alpha: E,
    mut word: impl FnMut(InitialIndex) -> E,
    u: FibreIndex,
) -> Result<E, Error> {
    let mut a = [E::ZERO; 4];
    for (s, value) in a.iter_mut().enumerate() {
        *value = word(domain::child_index(u, SlotIndex::new(s)?));
    }
    fold_fibre(alpha, u, a)
}
/// SPEC §4: foldMessage; channels q_s[d]=q[4d+s].
pub fn fold_message<E: CodeField>(alpha: E, q: &Message<E>) -> FinalMessage<E> {
    let mut out = [E::ZERO; 256];
    for (value, h) in out.iter_mut().zip(q.chunks_exact(4)) {
        *value = combine(alpha, [h[0], h[1], h[2], h[3]]);
    }
    out
}
/// SPEC §4: citedDualFold, powers [0,3,2,1], with NO quarter inside.
/// Valid also at alpha=0; there are no negative powers or inversions.
pub fn dual_fold<E: CodeField>(alpha: E, w: &Message<E>) -> FinalMessage<E> {
    let mut out = [E::ZERO; 256];
    for (value, h) in out.iter_mut().zip(w.chunks_exact(4)) {
        *value = combine(alpha, [h[0], h[3], h[2], h[1]]);
    }
    out
}
