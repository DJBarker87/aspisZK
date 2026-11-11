//! FUTURE-VERSION EXPERIMENT (branch `future-version`). UNPROVED, NOT ADOPTED,
//! not part of the pinned R1 verifier and not reachable from its entrypoints.
//! Design note and pre-registered criteria:
//! `docs/research/future-version/ONE-TX-EXPERIMENT.md`.
//!
//! Two single-invocation verifiers over the unchanged 57,607-byte proof:
//!
//! - `verify` (stage A): the pinned checks of `tx1` followed by `tx2`, with
//!   the state kept in memory instead of a checkpoint. Same acceptance
//!   predicate as the pinned pair on a proof whose checkpoint is the one
//!   `tx1` wrote.
//! - `verify_batched` (stage C): the second fold is rearranged exactly, and
//!   the 22 per-query first-fold equalities `F_i = b_i` are replaced by the one
//!   equality `sum_i rho^i F_i = sum_i rho^i b_i`, computed with the query
//!   accumulation done in QM31 before any WideExact product. THIS CHANGES THE
//!   ACCEPTANCE PREDICATE (see the cancellation test below and the note); it
//!   is a protocol change that needs its own soundness argument.
//!
//! Child module of `candidate`, so it reuses the pinned parsing, semantic
//! layer, transcript, multiproof and relation code without copying it.
use super::*;
use crate::compact::QUERIES;
use crate::fast_pairing::{EbyKDot, KbyKDot};

const P64: u64 = 0x7fff_ffff;

/// Stage A. Pinned mathematics, one invocation, no checkpoint.
#[inline(never)]
pub fn verify<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    parse_shape(proof)?;
    canonical_scan(proof)?;
    mark(obs, Phase::Parsed);
    let mut g = [E::ZERO; 29];
    let p = prepare(public, proof, hash, obs, &mut g)?;
    let a = Accumulator::new(Variant::S2)?;
    mark(obs, Phase::Prepare);
    let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    batch_merkle(proof, &p, &folded_root, 0, hash)?;
    mark(obs, Phase::Merkle(0));
    batch_merkle(proof, &p, &folded_root, 1, hash)?;
    mark(obs, Phase::Merkle(SPLIT));
    let geometry = QueryGeometry::for_range(&p.queries, 0, QUERIES)?;
    let pending = BatchedWeights::new(&a.weights)?;
    let (a, pending) = query_loop(proof, &p, a, &g, obs, &geometry, pending, QUERIES)?;
    let Accumulator { mut weights, rhs, power, next } = a;
    pending.finish(&mut weights);
    let a = Accumulator { weights, rhs, power, next };
    finish_relation(&relation_view(proof)?, &p, &a, obs)
}

/// Stage C. Batched first fold and rearranged second fold.
#[inline(never)]
pub fn verify_batched<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    parse_shape(proof)?;
    // The base-lane kernel below reads M31 limbs without re-checking them; it
    // relies on this scan having accepted every opening of this same buffer.
    canonical_scan(proof)?;
    mark(obs, Phase::Parsed);
    let mut g = [E::ZERO; 29];
    let p = prepare(public, proof, hash, obs, &mut g)?;
    let mut a = Accumulator::new(Variant::S2)?;
    mark(obs, Phase::Prepare);
    let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    batch_merkle(proof, &p, &folded_root, 0, hash)?;
    mark(obs, Phase::Merkle(0));
    batch_merkle(proof, &p, &folded_root, 1, hash)?;
    mark(obs, Phase::Merkle(SPLIT));
    let geometry = QueryGeometry::for_range(&p.queries, 0, QUERIES)?;
    let openings = &proof[compact::OFF_OPENINGS..compact::OFF_NODES];
    let sums = fold_sums(openings, &p.queries, p.rho, &p.alpha, &g, &geometry, obs)?;
    if sums.lhs1 != sums.rhs1 {
        return Err(Error::Query);
    }
    let mut pending = BatchedWeights::new(&a.weights)?;
    accumulate_weights(&p, &mut a, &geometry, &mut pending);
    pending.finish(&mut a.weights);
    a.rhs = sums.rhs2;
    mark(obs, Phase::QueryPart(0, 4));
    finish_relation(&relation_view(proof)?, &p, &a, obs)
}

fn relation_view(proof: &[u8]) -> Result<View<'_>, Error> {
    Ok(View {
        variant: Variant::S2,
        semantic: &[],
        y1: &[],
        inactive: E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: None,
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: &[],
    })
}

/// The three batched quantities of stage C.
///
/// With `F_i` the pinned first fold of query `i`, `b_i` its authenticated
/// folded value and `G_i` the pinned second fold:
/// `lhs1 = sum_i rho^i F_i`, `rhs1 = sum_i rho^i b_i`, `rhs2 = sum_i rho^i G_i`.
/// `rhs2` is the pinned accumulator `rhs` exactly; `lhs1 = rhs1` replaces the
/// 22 pinned equalities `F_i = b_i`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FoldSums {
    pub lhs1: E,
    pub rhs1: E,
    pub rhs2: E,
}

/// Per-query QM31 coefficients: `rho^i` times the base-field fold geometry.
struct Coefficients {
    /// `rho^i / 4 * [1, 1/y, 1/x, 1/(xy)]` at the circle point of query `i`.
    circle: Vec<[K; 4]>,
    /// `rho^i / 4 * [1, 1/x, 1/y, 1/z, 1/(zx), -1/(zy)]` at its line nodes.
    line: Vec<[K; 6]>,
    rho: Vec<K>,
}

#[inline(never)]
fn coefficients(rho: K, geometry: &QueryGeometry) -> Result<Coefficients, Error> {
    let mut line = aspis_core::r0::heap::filled(QUERIES, [K::ZERO; 6]).map_err(|_| Error::Allocation)?;
    let mut circle = aspis_core::r0::heap::filled(QUERIES, [K::ZERO; 4]).map_err(|_| Error::Allocation)?;
    let mut powers = aspis_core::r0::heap::filled(QUERIES, K::ZERO).map_err(|_| Error::Allocation)?;
    let mut power = K::ONE;
    for i in 0..QUERIES {
        let [ix, iy, lx, ly, lz] = *geometry.for_query(i);
        let r = power.mul_m31(QUARTER);
        circle[i] = [r, r.mul_m31(iy), r.mul_m31(ix), r.mul_m31(ix.mul(iy))];
        let rz = r.mul_m31(lz);
        line[i] = [r, r.mul_m31(lx), r.mul_m31(ly), rz, rz.mul_m31(lx), rz.mul_m31(ly).neg()];
        powers[i] = power;
        power = power.mul(rho);
    }
    Ok(Coefficients { circle, line, rho: powers })
}

/// One base-field lane: `H_k = sum_i c_{i,k} * S_k(v_i)` in QM31, where
/// `S_0..S_3` are the four signed sums of the lane's four slot values.
///
/// Precondition: every limb read is canonical (`< P`), which the caller's
/// `canonical_scan` established. Bounds: each signed sum is formed
/// nonnegative below `2^33`, folded and conditionally reduced to `< P`; each
/// limb product is then at most `(P-1)^2`, four of them plus a folded residue
/// below `2^34` stay below `2^64`, and the accumulator is folded after every
/// fourth query (the same cadence and bound as the pinned `BatchedWeights`).
#[inline(always)]
fn base_lane(openings: &[u8], circle: &[[K; 4]], lane: usize) -> [K; 4] {
    let mut acc = [[0u64; 4]; 4];
    let at = 4 * lane;
    for i in 0..QUERIES {
        let q = &openings[i * OPENING..i * OPENING + 480];
        let read = |s: usize| u64::from(u32::from_le_bytes(q[s * 120 + at..s * 120 + at + 4].try_into().unwrap()));
        let (v0, v1, v2, v3) = (read(0), read(1), read(2), read(3));
        let u = v0 + v1;
        let w = v2 + v3;
        let x = v0 + P64 - v1;
        let y = v3 + P64 - v2;
        let signed = [u + w, x + y, u + 2 * P64 - w, x + 2 * P64 - y];
        let c = &circle[i];
        for k in 0..4 {
            let mut s = (signed[k] & P64) + (signed[k] >> 31);
            if s >= P64 {
                s -= P64;
            }
            acc[k][0] += u64::from(c[k].c0.a.0) * s;
            acc[k][1] += u64::from(c[k].c0.b.0) * s;
            acc[k][2] += u64::from(c[k].c1.a.0) * s;
            acc[k][3] += u64::from(c[k].c1.b.0) * s;
        }
        if i & 3 == 3 {
            for row in &mut acc {
                for limb in row {
                    *limb = (*limb & P64) + (*limb >> 31);
                }
            }
        }
    }
    core::array::from_fn(|k| {
        let [a, b, c, d] = acc[k].map(M31::reduce_u64);
        K { c0: aspis_core::field::CM31 { a, b }, c1: aspis_core::field::CM31 { a: c, b: d } }
    })
}

/// One QM31 lane (`which` 0, 1: the two C2 lanes; 2: the C1 tail lane).
#[inline(always)]
fn extension_lane(openings: &[u8], circle: &[[K; 4]], which: usize) -> Result<[K; 4], Error> {
    let mut dots = [KbyKDot::new(), KbyKDot::new(), KbyKDot::new(), KbyKDot::new()];
    for i in 0..QUERIES {
        let q = &openings[i * OPENING..i * OPENING + 608];
        let read = |s: usize| {
            let at = if which == 2 { s * 120 + 104 } else { 480 + s * 32 + which * 16 };
            K::from_le_bytes(&q[at..at + 16]).ok_or(Error::Parse)
        };
        let (v0, v1, v2, v3) = (read(0)?, read(1)?, read(2)?, read(3)?);
        let u = v0.add(v1);
        let w = v2.add(v3);
        let x = v0.sub(v1);
        let y = v3.sub(v2);
        let signed = [u.add(w), x.add(y), u.sub(w), x.sub(y)];
        for k in 0..4 {
            dots[k].push(circle[i][k], signed[k]).map_err(|_| Error::Parse)?;
        }
    }
    let [d0, d1, d2, d3] = dots;
    Ok([d0.finish(), d1.finish(), d2.finish(), d3.finish()])
}

#[inline(always)]
fn cubic(alpha: E, h: [E; 4]) -> E {
    h[0].add(alpha.mul(h[1].add(alpha.mul(h[2].add(alpha.mul(h[3]))))))
}

/// The batched fold quantities over all 22 openings (`openings` is the
/// 22 x 832-byte opening section of the stored proof).
#[inline(never)]
fn fold_sums(openings: &[u8], queries: &[u32; 22], rho: K, alpha: &[E; 2], g: &[E; 29], geometry: &QueryGeometry, obs: Observer) -> Result<FoldSums, Error> {
    if openings.len() != QUERIES * OPENING {
        return Err(Error::Parse);
    }
    let c = coefficients(rho, geometry)?;
    mark(obs, Phase::QueryPart(0, 0));

    // First fold, left side: accumulate over the queries in QM31 lane by
    // lane, then contract each lane once with its gamma power.
    let mut first = [EbyKDot::new(), EbyKDot::new(), EbyKDot::new(), EbyKDot::new()];
    for lane in 0..26 {
        let h = base_lane(openings, &c.circle, lane);
        for k in 0..4 {
            first[k].push(g[lane], h[k]).map_err(|_| Error::Parse)?;
        }
    }
    mark(obs, Phase::QueryPart(0, 1));
    for which in 0..3 {
        let h = extension_lane(openings, &c.circle, which)?;
        // Pinned gamma indices: C2 lanes 26 and 27, C1 tail lane 28.
        let power = g[if which == 2 { 28 } else { 26 + which }];
        for k in 0..4 {
            first[k].push(power, h[k]).map_err(|_| Error::Parse)?;
        }
    }
    let [f0, f1, f2, f3] = first;
    let lhs1 = cubic(alpha[0], [f0.finish(), f1.finish(), f2.finish(), f3.finish()]);
    mark(obs, Phase::QueryPart(0, 2));

    // First fold, right side, and the second fold's four cubic coefficients.
    let mut second = [EbyKDot::new(), EbyKDot::new(), EbyKDot::new(), EbyKDot::new()];
    let mut right = EbyKDot::new();
    for i in 0..QUERIES {
        let q = &openings[i * OPENING..(i + 1) * OPENING];
        let v: [E; 4] = core::array::from_fn(|s| field(&q[672..800], s));
        let u = v[0].add(v[1]);
        let w = v[2].add(v[3]);
        let d1 = v[0].sub(v[1]);
        let d2 = v[3].sub(v[2]);
        let l = &c.line[i];
        let mut push = |dot: &mut EbyKDot, value: E, scalar: K| dot.push(value, scalar).map_err(|_| Error::Parse);
        push(&mut second[0], u.add(w), l[0])?;
        push(&mut second[1], d1, l[1])?;
        push(&mut second[1], d2, l[2])?;
        push(&mut second[2], u.sub(w), l[3])?;
        push(&mut second[3], d1, l[4])?;
        push(&mut second[3], d2, l[5])?;
        push(&mut right, v[queries[i] as usize % 4], c.rho[i])?;
    }
    let [t0, t1, t2, t3] = second;
    let rhs2 = cubic(alpha[1], [t0.finish(), t1.finish(), t2.finish(), t3.finish()]);
    mark(obs, Phase::QueryPart(0, 3));
    Ok(FoldSums { lhs1, rhs1: right.finish(), rhs2 })
}

/// The pinned final-weight accumulation `w_j += rho^i * basis_j(node_i)` for
/// all 22 queries (the weight half of `accumulate_batched_with_node`).
#[inline(never)]
fn accumulate_weights(p: &Prepared, a: &mut Accumulator, geometry: &QueryGeometry, weights: &mut BatchedWeights) {
    let width = a.weights.len();
    for i in 0..QUERIES {
        let z = geometry.line_z[i - geometry.start];
        let mut node = z.mul(z).double().sub(M31::ONE);
        let mut basis = [M31::ZERO; 256];
        basis[0] = M31::ONE;
        let mut n = 1;
        while n < width {
            for j in 0..n {
                basis[n + j] = basis[j].mul(node);
            }
            node = node.mul(node).double().sub(M31::ONE);
            n *= 2;
        }
        for j in 0..width {
            weights.push(j, a.power, basis[j]);
        }
        weights.terms += 1;
        a.power = a.power.mul(p.rho);
        a.next += 1;
    }
}

/// MEASUREMENT PROBE ONLY: it verifies nothing and its result has no meaning.
///
/// Cost of binding the opening section and the final message to one QM31
/// value through a product-form weight, `sum_{i,s,l} w_{i,s} * lambda_l *
/// a_{i,s,l}`, which is the shape of the input evaluation a sumcheck or GKR
/// certificate over the verifier's arithmetic would have to compute itself
/// (2,288 M31 values, 264 QM31 values and 88 + 64 WideExact values, the last
/// two as QM31 coordinates). The weights are arbitrary canonical QM31 values
/// read from the proof, so nothing is constant-folded. Challenges in QM31 are
/// the cheapest case; WideExact weights would cost about twice as much.
#[inline(never)]
pub fn input_evaluation_probe(proof: &[u8], obs: Observer) -> Result<K, Error> {
    parse_shape(proof)?;
    canonical_scan(proof)?;
    mark(obs, Phase::Parsed);
    let openings = &proof[compact::OFF_OPENINGS..compact::OFF_NODES];
    let final_message = &proof[compact::OFF_FINAL..compact::OFF_OPENINGS];
    let seed = K::from_le_bytes(&openings[104..120]).ok_or(Error::Parse)?;
    let other = K::from_le_bytes(&openings[480..496]).ok_or(Error::Parse)?;
    let mut w = [K::ZERO; 88];
    let mut lambda = [K::ZERO; 33];
    let mut power = K::ONE;
    for x in &mut w {
        *x = power;
        power = power.mul(seed);
    }
    power = K::ONE;
    for x in &mut lambda {
        *x = power;
        power = power.mul(other);
    }
    mark(obs, Phase::QueryPart(1, 0));
    let mut total = KbyKDot::new();
    let mut push = |a: K, b: K| total.push(a, b).map_err(|_| Error::Parse);
    for lane in 0..26 {
        let mut acc = [0u64; 4];
        for i in 0..QUERIES {
            let q = &openings[i * OPENING..i * OPENING + 480];
            for s in 0..4 {
                let v = u64::from(u32::from_le_bytes(q[s * 120 + 4 * lane..s * 120 + 4 * lane + 4].try_into().unwrap()));
                let c = &w[4 * i + s];
                acc[0] += u64::from(c.c0.a.0) * v;
                acc[1] += u64::from(c.c0.b.0) * v;
                acc[2] += u64::from(c.c1.a.0) * v;
                acc[3] += u64::from(c.c1.b.0) * v;
            }
            for limb in &mut acc {
                *limb = (*limb & P64) + (*limb >> 31);
            }
        }
        let [a, b, c, d] = acc.map(M31::reduce_u64);
        push(lambda[lane], K { c0: aspis_core::field::CM31 { a, b }, c1: aspis_core::field::CM31 { a: c, b: d } })?;
    }
    mark(obs, Phase::QueryPart(1, 1));
    for which in 0..3 {
        let mut dot = KbyKDot::new();
        for i in 0..QUERIES {
            let q = &openings[i * OPENING..i * OPENING + 608];
            for s in 0..4 {
                let at = if which == 2 { s * 120 + 104 } else { 480 + s * 32 + which * 16 };
                dot.push(w[4 * i + s], K::from_le_bytes(&q[at..at + 16]).ok_or(Error::Parse)?).map_err(|_| Error::Parse)?;
            }
        }
        push(lambda[26 + which], dot.finish())?;
    }
    mark(obs, Phase::QueryPart(1, 2));
    let mut folded = [KbyKDot::new(), KbyKDot::new()];
    for i in 0..QUERIES {
        let q = &openings[i * OPENING..(i + 1) * OPENING];
        for s in 0..4 {
            let e = field(&q[672..800], s);
            folded[0].push(w[4 * i + s], e.c0()).map_err(|_| Error::Parse)?;
            folded[1].push(w[4 * i + s], e.c1()).map_err(|_| Error::Parse)?;
        }
    }
    let mut last = [KbyKDot::new(), KbyKDot::new()];
    for j in 0..compact::FINAL_LEN {
        let e = field(final_message, j);
        last[0].push(w[j], e.c0()).map_err(|_| Error::Parse)?;
        last[1].push(w[j], e.c1()).map_err(|_| Error::Parse)?;
    }
    let [folded0, folded1] = folded;
    let [last0, last1] = last;
    push(lambda[29], folded0.finish())?;
    push(lambda[30], folded1.finish())?;
    push(lambda[31], last0.finish())?;
    push(lambda[32], last1.finish())?;
    mark(obs, Phase::QueryPart(1, 3));
    Ok(total.finish())
}

/// MEASUREMENT PROBE ONLY: unit costs of the field kernels, 512 chained
/// operations each, on operands read from the proof. Verifies nothing.
#[inline(never)]
pub fn unit_cost_probe(proof: &[u8], obs: Observer) -> Result<K, Error> {
    parse_shape(proof)?;
    canonical_scan(proof)?;
    let openings = &proof[compact::OFF_OPENINGS..compact::OFF_NODES];
    let final_message = &proof[compact::OFF_FINAL..compact::OFF_OPENINGS];
    let b = K::from_le_bytes(&openings[104..120]).ok_or(Error::Parse)?;
    let c = M31::from_le_bytes(openings[0..4].try_into().unwrap()).ok_or(Error::Parse)?;
    let e2 = field(final_message, 1);
    const N: usize = 512;
    mark(obs, Phase::QueryPart(2, 0));
    let mut x = K::from_le_bytes(&openings[480..496]).ok_or(Error::Parse)?;
    for _ in 0..N {
        x = x.mul(b);
    }
    mark(obs, Phase::QueryPart(2, 1)); // QM31::mul
    for _ in 0..N {
        x = crate::fast_pairing::k_mul_sixteen(x, b).map_err(|_| Error::Parse)?;
    }
    mark(obs, Phase::QueryPart(2, 2)); // 16-product QM31 multiplication
    let mut e = field(final_message, 0);
    for _ in 0..N {
        e = e.mul(e2);
    }
    mark(obs, Phase::QueryPart(2, 3)); // WideExact::mul
    for _ in 0..N {
        e = e.mul_qm31(b);
    }
    mark(obs, Phase::QueryPart(2, 4)); // WideExact::mul_qm31
    let mut m = c;
    for _ in 0..N {
        m = m.mul(c);
    }
    mark(obs, Phase::QueryPart(2, 5)); // M31::mul
    let mut dot = EbyKDot::new();
    for _ in 0..N {
        dot.push(e, x).map_err(|_| Error::Parse)?;
    }
    let pushed = dot.finish();
    mark(obs, Phase::QueryPart(2, 6)); // EbyKDot::push (same operands each time)
    let mut kdot = KbyKDot::new();
    for _ in 0..N {
        kdot.push(b, x).map_err(|_| Error::Parse)?;
    }
    let kpushed = kdot.finish();
    mark(obs, Phase::QueryPart(2, 7)); // KbyKDot::push
    Ok(x.add(pushed.c0()).add(e.c1()).add(kpushed).mul_m31(m))
}

/// MEASUREMENT PROBE ONLY (profiling builds): the pinned relation phase of an
/// accepting proof with a mark after each stage. It repeats the pinned
/// semantic layer and preparation to obtain the real challenges.
#[cfg(feature = "detail-phases")]
#[inline(never)]
pub fn relation_probe<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    parse_shape(proof)?;
    canonical_scan(proof)?;
    let mut g = [E::ZERO; 29];
    let p = prepare(public, proof, hash, None, &mut g)?;
    let v = relation_view(proof)?;
    mark(obs, Phase::QueryPart(3, 0));
    let mut claim = finish_relation_round(v.round0, p.alpha[0], p.claim, 0)?;
    claim = finish_relation_round(v.round1, p.alpha[1], claim, 1)?;
    mark(obs, Phase::QueryPart(3, 1)); // two round checks
    let weights = Weights::new(p.variant, &p.semantic_alpha, &p.z)?;
    mark(obs, Phase::QueryPart(3, 2)); // Weights::new
    let pair = weights.pair_marked(&p.alpha[..2], v.final_message, p.kappa, &|i| mark(obs, Phase::QueryPart(4, i)))?;
    if pair != claim {
        return Err(Error::Relation);
    }
    mark(obs, Phase::QueryPart(3, 3));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use aspis_core::field::{CM31, P};
    use aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1;
    use sha2::{Digest, Sha256};

    #[derive(Clone, Copy)]
    struct Sha;
    impl Digest32 for Sha {
        fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
            let mut d = Sha256::new();
            for part in parts {
                d.update(part);
            }
            d.finalize().into()
        }
    }

    macro_rules! fixture {
        ($name:literal) => {
            (
                $name,
                include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/", $name, "/r1-s2-proof.bin")) as &[u8],
                include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/", $name, "/r1-s2-public-asf8.bin")) as &[u8],
            )
        };
    }
    /// The six saved fixtures as regenerated at the PIN2 pin (c7593d23fdc).
    const FIXTURES: [(&str, &[u8], &[u8]); 6] = [
        fixture!("transfer-13"),
        fixture!("transfer-255"),
        fixture!("transfer-1023"),
        fixture!("withdrawal-13"),
        fixture!("withdrawal-255"),
        fixture!("withdrawal-1023"),
    ];

    fn next(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut value = *state;
        value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        value ^ (value >> 31)
    }
    fn limb(state: &mut u64, case: usize) -> u32 {
        match case {
            0 => 0,
            1 => 1,
            2 => P - 1,
            _ => (next(state) % u64::from(P)) as u32,
        }
    }
    fn random_k(state: &mut u64, case: usize) -> K {
        K { c0: CM31 { a: M31(limb(state, case)), b: M31(limb(state, case)) }, c1: CM31 { a: M31(limb(state, case)), b: M31(limb(state, case)) } }
    }
    fn random_e(state: &mut u64, case: usize) -> E {
        E::new(random_k(state, case), random_k(state, case))
    }
    fn distinct_queries(state: &mut u64) -> [u32; 22] {
        let mut out = [0u32; 22];
        let mut n = 0;
        while n < 22 {
            let q = (next(state) % (1 << 18)) as u32;
            if !out[..n].contains(&q) && QueryGeometry::for_range(&{ let mut one = [0u32; 22]; one[0] = q; one }, 0, 1).is_ok() {
                out[n] = q;
                n += 1;
            }
        }
        out
    }
    /// A canonical opening section with arbitrary values (no Merkle meaning).
    fn random_openings(state: &mut u64, case: usize) -> Vec<u8> {
        let mut out = vec![0u8; QUERIES * OPENING];
        for i in 0..QUERIES {
            let q = &mut out[i * OPENING..(i + 1) * OPENING];
            for s in 0..4 {
                for l in 0..26 {
                    q[s * 120 + l * 4..s * 120 + l * 4 + 4].copy_from_slice(&limb(state, case).to_le_bytes());
                }
                random_k(state, case).write_le_bytes(&mut q[s * 120 + 104..s * 120 + 120]);
                for l in 0..2 {
                    random_k(state, case).write_le_bytes(&mut q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]);
                }
                q[672 + s * 32..672 + s * 32 + 32].copy_from_slice(&random_e(state, case).to_le_bytes());
            }
        }
        out
    }

    /// The pinned per-query quantities, from the pinned kernels.
    fn reference(openings: &[u8], queries: &[u32; 22], rho: K, alpha: &[E; 2], g: &[E; 29], geometry: &QueryGeometry) -> (FoldSums, Vec<E>, Vec<E>) {
        let mut sums = FoldSums { lhs1: E::ZERO, rhs1: E::ZERO, rhs2: E::ZERO };
        let (mut first, mut authenticated) = (Vec::new(), Vec::new());
        let mut power = K::ONE;
        for i in 0..QUERIES {
            let q = &openings[i * OPENING..(i + 1) * OPENING];
            let inverse = *geometry.for_query(i);
            let f = circle_fold_with_inverses(alpha[0], crate::fast_dots::four_dots(q, g), &inverse);
            let values: [E; 4] = core::array::from_fn(|s| field(&q[672..800], s));
            let b = values[queries[i] as usize % 4];
            let second = line_fold_with_inverses(alpha[1], values, &inverse);
            sums.lhs1 = sums.lhs1.add(f.mul_qm31(power));
            sums.rhs1 = sums.rhs1.add(b.mul_qm31(power));
            sums.rhs2 = sums.rhs2.add(second.mul_qm31(power));
            first.push(f);
            authenticated.push(b);
            power = power.mul(rho);
        }
        (sums, first, authenticated)
    }

    #[test]
    fn batched_sums_equal_the_pinned_per_query_kernels_on_arbitrary_and_edge_inputs() {
        let mut state = 0x452821e638d01377u64;
        for case in 0..40 {
            let queries = distinct_queries(&mut state);
            let geometry = QueryGeometry::for_range(&queries, 0, 22).unwrap();
            let openings = random_openings(&mut state, case % 5);
            let rho = random_k(&mut state, (case / 5) % 4 + if case < 20 { 0 } else { 3 });
            let alpha = [random_e(&mut state, 3 + case % 2), random_e(&mut state, 2 + case % 3)];
            let g = powers::<29>(random_e(&mut state, if case % 7 == 0 { 2 } else { 3 }));
            let (expected, _, _) = reference(&openings, &queries, rho, &alpha, &g, &geometry);
            let actual = fold_sums(&openings, &queries, rho, &alpha, &g, &geometry, None).unwrap();
            assert_eq!(actual, expected, "case {case}");
        }
    }

    #[test]
    fn maximal_limbs_do_not_overflow_the_delayed_accumulators() {
        let mut state = 7;
        let queries = distinct_queries(&mut state);
        let geometry = QueryGeometry::for_range(&queries, 0, 22).unwrap();
        let openings = random_openings(&mut state, 2);
        let max_k = random_k(&mut state, 2);
        let max_e = E::new(max_k, max_k);
        let g = [max_e; 29];
        for rho in [max_k, K::ONE, K::ZERO] {
            let (expected, _, _) = reference(&openings, &queries, rho, &[max_e, max_e], &g, &geometry);
            assert_eq!(fold_sums(&openings, &queries, rho, &[max_e, max_e], &g, &geometry, None).unwrap(), expected);
        }
    }

    fn decode(public: &[u8]) -> aspis_statement::pool_v1::PoolV1PairForestTerminalStatementV1 {
        decode_pool_v1_pair_forest_terminal_statement_v1(public).unwrap()
    }

    #[test]
    fn all_three_verifiers_accept_the_six_pin2_fixtures() {
        for (name, proof, public) in FIXTURES {
            let statement = decode(public);
            let checkpoint = tx1(statement.semantic_public(), public, proof, SPLIT, Sha, None).unwrap_or_else(|e| panic!("{name} tx1 {e:?}"));
            tx2(public, proof, &checkpoint, Sha, None).unwrap_or_else(|e| panic!("{name} tx2 {e:?}"));
            verify(statement.semantic_public(), proof, Sha, None).unwrap_or_else(|e| panic!("{name} fused {e:?}"));
            verify_batched(statement.semantic_public(), proof, Sha, None).unwrap_or_else(|e| panic!("{name} batched {e:?}"));
        }
    }

    /// Byte positions whose mutation must be rejected: one per proof region.
    fn mutation_offsets() -> Vec<usize> {
        let o = compact::OFF_OPENINGS;
        vec![
            compact::OFF_SEMANTIC + 40,
            compact::OFF_Y1 + 3,
            compact::OFF_INACTIVE + 1,
            compact::OFF_ROUND0 + 5,
            compact::OFF_FOLDED_ROOT + 7,
            compact::OFF_ROUND1 + 9,
            compact::OFF_FINAL + 11,
            compact::OFF_FINAL + 63 * 32,
            o,                         // query 0, C1 base lane
            o + 104,                   // query 0, C1 tail lane
            o + 480,                   // query 0, C2 lane
            o + 608,                   // query 0, C1 salt
            o + 672,                   // query 0, folded value
            o + 800,                   // query 0, folded salt
            o + 9 * OPENING + 4,       // last query of the first batch
            o + 10 * OPENING + 8,      // first query of the second batch
            o + 21 * OPENING + 676,    // last query, folded value
            compact::OFF_NODES + 1,
            compact::slot_offset(3) + 2,
            compact::slot_offset(5) + 33,
        ]
    }

    #[test]
    fn the_three_verifiers_reject_the_same_single_byte_mutations() {
        let (_, proof, public) = FIXTURES[0];
        let statement = decode(public);
        for at in mutation_offsets() {
            let mut bad = proof.to_vec();
            bad[at] ^= 1;
            let pinned = tx1(statement.semantic_public(), public, &bad, SPLIT, Sha, None).and_then(|c| tx2(public, &bad, &c, Sha, None));
            assert!(pinned.is_err(), "pinned accepted a mutation at {at}");
            assert!(verify(statement.semantic_public(), &bad, Sha, None).is_err(), "fused accepted a mutation at {at}");
            assert!(verify_batched(statement.semantic_public(), &bad, Sha, None).is_err(), "batched accepted a mutation at {at}");
        }
    }

    /// Recover the prepared challenges of a fixture (accepting run).
    fn prepared(proof: &[u8], public: &[u8]) -> (Box<Prepared>, [E; 29]) {
        let statement = decode(public);
        let mut g = [E::ZERO; 29];
        let p = prepare(statement.semantic_public(), proof, Sha, None, &mut g).unwrap();
        (p, g)
    }

    #[test]
    fn the_batched_first_fold_check_alone_rejects_any_single_opening_change() {
        // Merkle authentication is deliberately left out here: this exercises
        // the batched equality itself on an otherwise accepting fixture.
        let (_, proof, public) = FIXTURES[3];
        let (p, g) = prepared(proof, public);
        let geometry = QueryGeometry::for_range(&p.queries, 0, 22).unwrap();
        let openings = proof[compact::OFF_OPENINGS..compact::OFF_NODES].to_vec();
        let honest = fold_sums(&openings, &p.queries, p.rho, &p.alpha, &g, &geometry, None).unwrap();
        assert_eq!(honest.lhs1, honest.rhs1);
        for query in [0usize, 9, 10, 21] {
            // One base lane, the C1 tail lane, one C2 lane, in each slot.
            for at in (0..4).flat_map(|s| [s * 120 + 4 * (query % 26), s * 120 + 104, 480 + s * 32 + 16]) {
                let mut bad = openings.clone();
                let b = &mut bad[query * OPENING + at];
                *b = if *b == 0 { 1 } else { *b - 1 }; // stays canonical
                let sums = fold_sums(&bad, &p.queries, p.rho, &p.alpha, &g, &geometry, None).unwrap();
                assert_ne!(sums.lhs1, sums.rhs1, "query {query} offset {at}");
                assert_eq!(sums.rhs2, honest.rhs2);
            }
        }
    }

    /// TEETH VECTOR for the changed acceptance predicate. Given `rho`, two
    /// authenticated folded values can be changed so that the two first-fold
    /// residuals are nonzero and cancel at `rho`: the batched equality holds
    /// while the pinned per-query equality fails at both queries. Soundness
    /// of stage C therefore rests on the residuals being fixed by the
    /// commitments before `rho` is drawn, not on the check being exact.
    #[test]
    fn rho_dependent_cancellation_passes_the_batched_check_and_fails_the_pinned_one() {
        let (_, proof, public) = FIXTURES[1];
        let (p, g) = prepared(proof, public);
        let geometry = QueryGeometry::for_range(&p.queries, 0, 22).unwrap();
        let mut openings = proof[compact::OFF_OPENINGS..compact::OFF_NODES].to_vec();
        // Residuals r_3 = delta and r_4 = -delta / rho: r_3 rho^3 + r_4 rho^4 = 0.
        let delta = E::from_qm31(K::ONE);
        let rho_inverse = p.rho.try_inv().unwrap();
        for (query, shift) in [(3usize, delta), (4, delta.mul_qm31(rho_inverse).neg())] {
            let slot = p.queries[query] as usize % 4;
            let at = query * OPENING + 672 + 32 * slot;
            let old = E::from_le_bytes(&openings[at..at + 32]).unwrap();
            openings[at..at + 32].copy_from_slice(&old.add(shift).to_le_bytes());
        }
        let sums = fold_sums(&openings, &p.queries, p.rho, &p.alpha, &g, &geometry, None).unwrap();
        assert_eq!(sums.lhs1, sums.rhs1, "the crafted residuals cancel at rho");
        let (_, first, authenticated) = reference(&openings, &p.queries, p.rho, &p.alpha, &g, &geometry);
        assert_ne!(first[3], authenticated[3]);
        assert_ne!(first[4], authenticated[4]);
        // At any other challenge the same data is rejected.
        let other = p.rho.add(K::ONE);
        let moved = fold_sums(&openings, &p.queries, other, &p.alpha, &g, &geometry, None).unwrap();
        assert_ne!(moved.lhs1, moved.rhs1);
    }

    #[test]
    fn input_evaluation_probe_equals_the_naive_weighted_sum() {
        let (_, proof, _) = FIXTURES[2];
        let openings = &proof[compact::OFF_OPENINGS..compact::OFF_NODES];
        let seed = K::from_le_bytes(&openings[104..120]).unwrap();
        let other = K::from_le_bytes(&openings[480..496]).unwrap();
        let w: Vec<K> = (0..88).scan(K::ONE, |p, _| { let x = *p; *p = p.mul(seed); Some(x) }).collect();
        let lambda: Vec<K> = (0..33).scan(K::ONE, |p, _| { let x = *p; *p = p.mul(other); Some(x) }).collect();
        let mut expected = K::ZERO;
        for i in 0..22 {
            let q = &openings[i * OPENING..(i + 1) * OPENING];
            for s in 0..4 {
                let c = w[4 * i + s];
                for l in 0..26 {
                    let v = M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).unwrap();
                    expected = expected.add(c.mul(lambda[l]).mul_m31(v));
                }
                for l in 0..2 {
                    expected = expected.add(c.mul(lambda[26 + l]).mul(K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).unwrap()));
                }
                expected = expected.add(c.mul(lambda[28]).mul(K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).unwrap()));
                let e = field(&q[672..800], s);
                expected = expected.add(c.mul(lambda[29]).mul(e.c0())).add(c.mul(lambda[30]).mul(e.c1()));
            }
        }
        for j in 0..64 {
            let e = field(&proof[compact::OFF_FINAL..compact::OFF_OPENINGS], j);
            expected = expected.add(w[j].mul(lambda[31]).mul(e.c0())).add(w[j].mul(lambda[32]).mul(e.c1()));
        }
        assert_eq!(input_evaluation_probe(proof, None).unwrap(), expected);
    }

    #[cfg(feature = "detail-phases")]
    #[test]
    fn marked_pairing_equals_the_pinned_pairing_and_the_relation_probe_accepts() {
        for (name, proof, public) in FIXTURES {
            let (p, _) = prepared(proof, public);
            let weights = Weights::new(p.variant, &p.semantic_alpha, &p.z).unwrap();
            let f = &proof[compact::OFF_FINAL..compact::OFF_OPENINGS];
            assert_eq!(weights.pair_marked(&p.alpha[..2], f, p.kappa, &|_| ()).unwrap(), weights.pair(&p.alpha[..2], f, p.kappa).unwrap(), "{name}");
            relation_probe(decode(public).semantic_public(), proof, Sha, None).unwrap();
        }
    }

    #[test]
    fn sixteen_product_multiplication_is_the_field_product() {
        let mut state = 99;
        for case in 0..200 {
            let (a, b) = (random_k(&mut state, case % 5), random_k(&mut state, (case / 5) % 5));
            assert_eq!(crate::fast_pairing::k_mul_sixteen(a, b).unwrap(), a.mul(b));
        }
        unit_cost_probe(FIXTURES[0].1, None).unwrap();
    }
}
