//! Ownership-only candidate: preserve the existing dual and chord formulas.
use super::{basis_transport::transport, corelib::field::{QM31 as K, M31, M31_HALF}};

pub(super) fn dual(mut w: Vec<K>) -> Vec<K> {
    assert_eq!(w.len(), 1024);
    let map = transport();
    let pivot = w[1023];
    for r in 0..1023 {
        if map.inactive[r] { w[r] = w[r].sub(pivot); }
    }
    // Gather by the fixed, source-checked permutation in place.
    let mut seen = [false; 1024];
    for start in 0..1024 {
        if seen[start] { continue; }
        let saved = w[start];
        let mut at = start;
        loop {
            seen[at] = true;
            let next = map.order[at];
            if next == start { w[at] = saved; break; }
            w[at] = w[next];
            at = next;
        }
    }
    w
}

fn xt_at(mut value: impl FnMut(usize) -> K, j: usize) -> K {
    let (mut row, mut bit, mut scale, mut sum) = (j, 0, M31::ONE, K::ZERO);
    while row & (1 << bit) != 0 {
        row ^= 1 << bit;
        scale = scale.mul(M31_HALF);
        sum = sum.add(value(row).mul_m31(scale));
        bit += 1;
    }
    sum.add(value(row | (1 << bit)).mul_m31(scale))
}

pub(super) fn chord(mut w: Vec<K>, [a,b,c]: [K;3]) -> Vec<K> {
    assert_eq!(w.len(), 1024);
    // Same zero-padded even/odd projections, without allocating those projections
    // or cloning/growing w. Retain every intermediate needed before overwriting w.
    let xwa: Vec<_> = (0..513).map(|j| xt_at(|i|
        if i < 512 { w[2*i] } else { K::ZERO }, j)).collect();
    let xxwa: Vec<_> = (0..512).map(|j| xt_at(|i| xwa[i], j)).collect();
    let xwb: Vec<_> = (0..512).map(|j| xt_at(|i|
        if i < 512 { w[2*i+1] } else { K::ZERO }, j)).collect();
    for j in 0..512 {
        let even = w[2*j];
        let odd = w[2*j+1];
        w[2*j] = a.mul(even).add(b.mul(xwa[j])).add(c.mul(odd));
        w[2*j+1] = c.mul(even.sub(xxwa[j])).add(a.mul(odd)).add(b.mul(xwb[j]));
    }
    w
}
