//! Shared research opening weights, used verbatim by focused tests and host.
use super::{
    basis_transport::{transport, N},
    corelib::{
        field::{M31, M31_HALF, QM31 as K},
        sumcheck::WeightAccumulator,
        v6_transcript::v6_statement_points,
    },
};

fn xt(v: &[K], n: usize) -> Vec<K> {
    (0..n)
        .map(|j| {
            let (mut row, mut bit, mut scale, mut sum) = (j, 0, M31::ONE, K::ZERO);
            while row & (1 << bit) != 0 {
                row ^= 1 << bit;
                scale = scale.mul(M31_HALF);
                sum = sum.add(v[row].mul_m31(scale));
                bit += 1;
            }
            sum.add(v[row | (1 << bit)].mul_m31(scale))
        })
        .collect()
}
pub(super) fn chord_transpose(w: &[K], [a, b, c]: [K; 3]) -> Vec<K> {
    assert_eq!(w.len(), N);
    let mut w = w.to_vec();
    w.resize(1028, K::ZERO);
    let wa: Vec<_> = w.chunks_exact(2).map(|v| v[0]).collect();
    let wb: Vec<_> = w.chunks_exact(2).map(|v| v[1]).collect();
    let xwa = xt(&wa, 513);
    let xxwa = xt(&xwa, 512);
    let xwb = xt(&wb, 512);
    let mut out = vec![K::ZERO; N];
    for j in 0..512 {
        out[2 * j] = a.mul(wa[j]).add(b.mul(xwa[j])).add(c.mul(wb[j]));
        out[2 * j + 1] = c
            .mul(wa[j].sub(xxwa[j]))
            .add(a.mul(wb[j]))
            .add(b.mul(xwb[j]));
    }
    out
}
pub(super) fn original_weights(z: &[K; 10], kappa: K, structured: bool) -> Vec<K> {
    let scales = [kappa, kappa.square(), kappa.square().mul(kappa)];
    let mut w = WeightAccumulator::empty(10);
    for (i, p) in v6_statement_points(z).into_iter().enumerate() {
        if !(structured && i == 0) {
            w.add_multilinear(scales[i], p.to_vec()).unwrap();
        }
    }
    let g = structured.then(|| super::structured_g::mask_weights(z));
    (0..N)
        .map(|i| {
            let mut v = w.weight_at(i as u32);
            if transport().inactive[i] {
                v = v.add(K::ONE);
            }
            if let Some(g) = &g {
                v = v.add(kappa.mul(g[i]));
            }
            v
        })
        .collect()
}
pub(super) fn quotient_weights(
    z: &[K; 10],
    kappa: K,
    abc: [K; 3],
    tau: K,
    structured: bool,
) -> WeightAccumulator {
    let mut w = chord_transpose(
        &transport().dual(&original_weights(z, kappa, structured)),
        abc,
    );
    let t = if structured { tau.pow(3) } else { tau };
    let tt = if structured { tau.pow(4) } else { tau.square() };
    w[1023] = w[1023].add(t);
    w[1022] = w[1022].add(tt.mul(abc[1]));
    w[1021] = w[1021].sub(tt.mul(abc[2]));
    let mut out = WeightAccumulator::empty(10);
    out.add_dense(w).unwrap();
    out
}
