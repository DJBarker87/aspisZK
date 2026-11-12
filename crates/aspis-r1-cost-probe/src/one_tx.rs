//! Aspis one-transaction verifier. UNPROVED: no security claim is established
//! for it. Not reachable from the two-transaction (R1) verifier's entrypoints.
//! Design notes and the freeze record:
//! `docs/research/future-version/ONE-TX-EXPERIMENT.md`, `ASPIS-FREEZE.md`.
//!
//! Two single-invocation verifiers over the unchanged 57,607-byte proof:
//!
//! - `verify_unbatched` (stage A): the pinned checks of `tx1` followed by `tx2`, with
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
use crate::transcript::Transcript;

/// Profiling hook of the one-transaction functions. With `phase-observer` it carries the observer; without it
/// (every deployed build) it is a zero-sized value, so no function-pointer type is on the on-chain path.
#[cfg(feature = "phase-observer")]
#[derive(Clone, Copy)]
pub(crate) struct Hook(Observer);
#[cfg(not(feature = "phase-observer"))]
#[derive(Clone, Copy)]
pub(crate) struct Hook;
impl Hook {
    #[cfg(feature = "phase-observer")]
    pub(crate) const NONE: Hook = Hook(None);
    #[cfg(not(feature = "phase-observer"))]
    pub(crate) const NONE: Hook = Hook;
    /// From an observer. Without `phase-observer` the observer is dropped.
    #[cfg(feature = "phase-observer")]
    #[inline(always)]
    pub(crate) fn of(obs: Observer) -> Self {
        Hook(obs)
    }
    #[cfg(not(feature = "phase-observer"))]
    #[inline(always)]
    pub(crate) fn of(obs: Observer) -> Self {
        let _ = obs;
        Hook
    }
    #[cfg(feature = "phase-observer")]
    #[inline(always)]
    fn note(self, phase: Phase) {
        mark(self.0, phase)
    }
    #[cfg(not(feature = "phase-observer"))]
    #[inline(always)]
    fn note(self, phase: Phase) {
        let _ = phase;
    }
}

const P64: u64 = 0x7fff_ffff;

/// Stage A. Pinned mathematics, one invocation, no checkpoint.
#[inline(never)]
pub fn verify_unbatched<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
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
    let sums = fold_sums(openings, &p.queries, p.rho, &p.alpha, &g, &geometry, Hook::of(obs))?;
    if sums.lhs1 != sums.rhs1 {
        return Err(Error::Query);
    }
    let mut pending = BatchedWeights::new(&a.weights)?;
    if cfg!(feature = "tight-weights") {
        accumulate_weights_tight(&p, &mut a, &geometry, &mut pending)?;
    } else {
        accumulate_weights(&p, &mut a, &geometry, &mut pending);
    }
    pending.finish(&mut a.weights);
    a.rhs = sums.rhs2;
    mark(obs, Phase::QueryPart(0, 4));
    finish_relation(&relation_view(proof)?, &p, &a, obs)
}

const NO_BYTES: &[u8] = &[];
fn relation_view(proof: &[u8]) -> Result<View<'_>, Error> {
    let inactive = E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?;
    Ok(View {
        variant: Variant::S2,
        semantic: NO_BYTES,
        y1: NO_BYTES,
        inactive,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: None,
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: NO_BYTES,
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
        #[cfg(feature = "fold-shared")]
        {
            // G6 uses only the first and fourth entries.
            let _ = (lx, ly);
            line[i] = [r, K::ZERO, K::ZERO, rz, K::ZERO, K::ZERO];
        }
        #[cfg(not(feature = "fold-shared"))]
        {
            line[i] = [r, r.mul_m31(lx), r.mul_m31(ly), rz, rz.mul_m31(lx), rz.mul_m31(ly).neg()];
        }
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

/// A QM31 opening value read from its four little-endian limbs at `at`, without a second
/// canonicality check. Precondition (as for the base-lane kernel): the caller's `canonical_scan`
/// accepted these bytes, so every limb is below P and the value equals `K::from_le_bytes`.
#[inline(always)]
fn scanned_k(q: &[u8; 608], at: usize) -> K {
    let limb = |o: usize| M31(u32::from_le_bytes([q[o], q[o + 1], q[o + 2], q[o + 3]]));
    K { c0: aspis_core::field::CM31 { a: limb(at), b: limb(at + 4) }, c1: aspis_core::field::CM31 { a: limb(at + 8), b: limb(at + 12) } }
}

/// One QM31 lane (`which` 0, 1: the two C2 lanes; 2: the C1 tail lane).
/// Precondition: `canonical_scan` accepted the openings (the values are read with `scanned_k`).
#[inline(always)]
fn extension_lane(openings: &[u8], circle: &[[K; 4]], which: usize) -> Result<[K; 4], Error> {
    let mut dots = [KbyKDot::new(), KbyKDot::new(), KbyKDot::new(), KbyKDot::new()];
    for i in 0..QUERIES {
        // A fixed-size view, as in `base_accumulate`, so that the limb offsets are checked at compile time.
        let q: &[u8; 608] = openings[i * OPENING..i * OPENING + 608].try_into().map_err(|_| Error::Parse)?;
        let at = |s: usize| if which == 2 { s * 120 + 104 } else { 480 + s * 32 + which * 16 };
        let (v0, v1, v2, v3) = (scanned_k(q, at(0)), scanned_k(q, at(1)), scanned_k(q, at(2)), scanned_k(q, at(3)));
        let u = v0.add(v1);
        let w = v2.add(v3);
        let x = v0.sub(v1);
        let y = v3.sub(v2);
        let signed = [u.add(w), x.add(y), u.sub(w), x.sub(y)];
        push_k4(&mut dots, &circle[i], &signed)?;
    }
    Ok([dots[0].value(), dots[1].value(), dots[2].value(), dots[3].value()])
}

#[inline(always)]
fn push_k4(dots: &mut [KbyKDot; 4], c: &[K; 4], signed: &[K; 4]) -> Result<(), Error> {
    for k in 0..4 {
        match dots[k].push(c[k], signed[k]) { Ok(()) => {}, Err(_) => return Err(Error::Parse) }
    }
    Ok(())
}
#[inline(always)]
fn push_e4(dots: &mut [EbyKDot; 4], power: E, h: &[K; 4]) -> Result<(), Error> {
    for k in 0..4 {
        match dots[k].push(power, h[k]) { Ok(()) => {}, Err(_) => return Err(Error::Parse) }
    }
    Ok(())
}
#[inline(always)]
fn push_e(dot: &mut EbyKDot, value: E, scalar: K) -> Result<(), Error> {
    match dot.push(value, scalar) { Ok(()) => Ok(()), Err(_) => Err(Error::Parse) }
}
#[inline(always)]
fn finish_e4(dots: &[EbyKDot; 4]) -> [E; 4] {
    [dots[0].value(), dots[1].value(), dots[2].value(), dots[3].value()]
}
/// First fold, left side, base lanes: each lane contracted once with its gamma power.
#[inline(always)]
fn first_fold_base(first: &mut [EbyKDot; 4], g: &[E; 29], h: &[[K; 4]]) -> Result<(), Error> {
    for lane in 0..26 {
        push_e4(first, g[lane], &h[lane])?;
    }
    Ok(())
}
/// First fold, left side, the three QM31 lanes. Pinned gamma indices: C2 lanes 26 and 27, C1 tail lane 28.
#[inline(always)]
fn first_fold_extension(first: &mut [EbyKDot; 4], g: &[E; 29], extension: &[[K; 4]; 3]) -> Result<(), Error> {
    for which in 0..3 {
        let power = g[if which == 2 { 28 } else { 26 + which }];
        push_e4(first, power, &extension[which])?;
    }
    Ok(())
}
/// First fold, right side, and the second fold's four cubic coefficients (the per-query loop of `fold_sums`).
#[inline(always)]
fn second_fold(openings: &[u8], queries: &[u32; 22], c: &Coefficients, geometry: &QueryGeometry, second: &mut [EbyKDot; 4], right: &mut EbyKDot) -> Result<(), Error> {
    for i in 0..QUERIES {
        let q = &openings[i * OPENING..(i + 1) * OPENING];
        let v: [E; 4] = core::array::from_fn(|s| field(&q[672..800], s));
        let u = v[0].add(v[1]);
        let w = v[2].add(v[3]);
        let d1 = v[0].sub(v[1]);
        let d2 = v[3].sub(v[2]);
        let l = &c.line[i];
        #[cfg(feature = "fold-shared")]
        {
            let [_, _, lx, ly, _] = *geometry.for_query(i);
            let p1 = d1.mul_m31(lx);
            let p2 = d2.mul_m31(ly);
            push_e(&mut second[0], u.add(w), l[0])?;
            push_e(&mut second[1], p1.add(p2), l[0])?;
            push_e(&mut second[2], u.sub(w), l[3])?;
            push_e(&mut second[3], p1.sub(p2), l[3])?;
        }
        #[cfg(not(feature = "fold-shared"))]
        {
            let _ = geometry;
            push_e(&mut second[0], u.add(w), l[0])?;
            push_e(&mut second[1], d1, l[1])?;
            push_e(&mut second[1], d2, l[2])?;
            push_e(&mut second[2], u.sub(w), l[3])?;
            push_e(&mut second[3], d1, l[4])?;
            push_e(&mut second[3], d2, l[5])?;
        }
        push_e(right, v[queries[i] as usize % 4], c.rho[i])?;
    }
    Ok(())
}

#[inline(always)]
fn cubic(alpha: E, h: [E; 4]) -> E {
    h[0].add(alpha.mul(h[1].add(alpha.mul(h[2].add(alpha.mul(h[3]))))))
}

/// The batched fold quantities over all 22 openings (`openings` is the
/// 22 x 832-byte opening section of the stored proof).
#[inline(never)]
fn fold_sums(openings: &[u8], queries: &[u32; 22], rho: K, alpha: &[E; 2], g: &[E; 29], geometry: &QueryGeometry, hook: Hook) -> Result<FoldSums, Error> {
    if openings.len() != QUERIES * OPENING {
        return Err(Error::Parse);
    }
    let c = coefficients(rho, geometry)?;
    hook.note(Phase::QueryPart(0, 0));
    let mut first = [EbyKDot::new(), EbyKDot::new(), EbyKDot::new(), EbyKDot::new()];
    #[cfg(feature = "tight-base")]
    {
        let h = base_lanes_tight(openings, &c.circle)?;
        first_fold_base(&mut first, g, &h)?;
    }
    #[cfg(not(feature = "tight-base"))]
    {
        let mut h = [[K::ZERO; 4]; 26];
        for lane in 0..26 {
            h[lane] = base_lane(openings, &c.circle, lane);
        }
        first_fold_base(&mut first, g, &h)?;
    }
    hook.note(Phase::QueryPart(0, 1));
    let extension = [extension_lane(openings, &c.circle, 0)?, extension_lane(openings, &c.circle, 1)?, extension_lane(openings, &c.circle, 2)?];
    first_fold_extension(&mut first, g, &extension)?;
    let lhs1 = cubic(alpha[0], finish_e4(&first));
    hook.note(Phase::QueryPart(0, 2));
    let mut second = [EbyKDot::new(), EbyKDot::new(), EbyKDot::new(), EbyKDot::new()];
    let mut right = EbyKDot::new();
    second_fold(openings, queries, &c, geometry, &mut second, &mut right)?;
    let rhs2 = cubic(alpha[1], finish_e4(&second));
    hook.note(Phase::QueryPart(0, 3));
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

#[inline(always)]
fn k_of(limbs: [u64; 4]) -> K {
    K {
        c0: aspis_core::field::CM31 { a: M31::reduce_u64(limbs[0]), b: M31::reduce_u64(limbs[1]) },
        c1: aspis_core::field::CM31 { a: M31::reduce_u64(limbs[2]), b: M31::reduce_u64(limbs[3]) },
    }
}

/// E5: all 26 base-field lanes in one pass, queries outermost. Same sums as
/// `base_lane` for every lane.
///
/// Precondition as for `base_lane` (canonical limbs, from the caller's scan).
/// Bounds: each signed sum is nonnegative below `2^33` and folded once to at
/// most `P + 3`; a product with a canonical limb is at most
/// `(P-1)(P+3) = 2^62 - 4`; the accumulators are folded after every third
/// query, so each holds at most three products plus a folded residue below
/// `2^34`, which is below `2^64`.
#[inline(always)]
fn base_query(acc: &mut [u64; 416], q: &[u8; 480], c: &[K; 4]) {
    let mut l = [0u64; 16];
    for k in 0..4 {
        l[4 * k] = u64::from(c[k].c0.a.0);
        l[4 * k + 1] = u64::from(c[k].c0.b.0);
        l[4 * k + 2] = u64::from(c[k].c1.a.0);
        l[4 * k + 3] = u64::from(c[k].c1.b.0);
    }
    for lane in 0..26 {
        let at = 4 * lane;
        let read = |o: usize| u64::from(u32::from_le_bytes([q[o], q[o + 1], q[o + 2], q[o + 3]]));
        let (v0, v1, v2, v3) = (read(at), read(120 + at), read(240 + at), read(360 + at));
        let u = v0 + v1;
        let w = v2 + v3;
        let x = v0 + P64 - v1;
        let y = v3 + P64 - v2;
        let fold = |z: u64| (z & P64) + (z >> 31u32);
        let signed = [fold(u + w), fold(x + y), fold(u + 2 * P64 - w), fold(x + 2 * P64 - y)];
        let base = 16 * lane;
        for k in 0..4 {
            for j in 0..4 {
                acc[base + 4 * k + j] += l[4 * k + j] * signed[k];
            }
        }
    }
}
/// The periodic fold of every accumulator, eight per step (same operation on each entry as a
/// one-entry loop; the loop overhead is paid once per eight).
#[inline(always)]
fn base_fold(acc: &mut [u64; 416]) {
    let mut t = 0;
    while t < 52 {
        let b = 8 * t;
        acc[b] = (acc[b] & P64) + (acc[b] >> 31u32);
        acc[b + 1] = (acc[b + 1] & P64) + (acc[b + 1] >> 31u32);
        acc[b + 2] = (acc[b + 2] & P64) + (acc[b + 2] >> 31u32);
        acc[b + 3] = (acc[b + 3] & P64) + (acc[b + 3] >> 31u32);
        acc[b + 4] = (acc[b + 4] & P64) + (acc[b + 4] >> 31u32);
        acc[b + 5] = (acc[b + 5] & P64) + (acc[b + 5] >> 31u32);
        acc[b + 6] = (acc[b + 6] & P64) + (acc[b + 6] >> 31u32);
        acc[b + 7] = (acc[b + 7] & P64) + (acc[b + 7] >> 31u32);
        t += 1;
    }
}
#[inline(always)]
fn base_accumulate(acc: &mut [u64; 416], openings: &[u8], circle: &[[K; 4]]) -> Result<(), Error> {
    for i in 0..QUERIES {
        let q: &[u8; 480] = openings[i * OPENING..i * OPENING + 480].try_into().map_err(|_| Error::Parse)?;
        base_query(acc, q, &circle[i]);
        if i % 3 == 2 {
            base_fold(acc);
        }
    }
    Ok(())
}
#[inline(never)]
fn base_lanes_tight(openings: &[u8], circle: &[[K; 4]]) -> Result<Vec<[K; 4]>, Error> {
    let mut acc = aspis_core::r0::heap::filled(26 * 16, 0u64).map_err(|_| Error::Allocation)?;
    {
        let acc: &mut [u64; 416] = match (&mut acc[..]).try_into() {
            Ok(array) => array,
            Err(_) => return Err(Error::Allocation),
        };
        base_accumulate(acc, openings, circle)?;
    }
    let mut out = aspis_core::r0::heap::filled(26, [K::ZERO; 4]).map_err(|_| Error::Allocation)?;
    for lane in 0..26 {
        for k in 0..4 {
            let at = 16 * lane + 4 * k;
            out[lane][k] = k_of([acc[at], acc[at + 1], acc[at + 2], acc[at + 3]]);
        }
    }
    Ok(out)
}

/// E6: the three QM31 lanes with the four signed sums formed on raw limbs and
/// reduced once, in place of four checked decodes and eight canonical QM31
/// additions per lane and query. Same sums as `extension_lane`. Precondition:
/// canonical limbs, from the caller's scan.
#[inline(never)]
fn extension_lanes_tight(openings: &[u8], circle: &[[K; 4]]) -> Result<[[K; 4]; 3], Error> {
    let mut dots: [[KbyKDot; 4]; 3] = core::array::from_fn(|_| core::array::from_fn(|_| KbyKDot::new()));
    for i in 0..QUERIES {
        let q: &[u8; 608] = openings[i * OPENING..i * OPENING + 608].try_into().map_err(|_| Error::Parse)?;
        for which in 0..3 {
            let offset = |s: usize| if which == 2 { s * 120 + 104 } else { 480 + s * 32 + which * 16 };
            let mut signed = [[0u64; 4]; 4];
            for j in 0..4 {
                let read = |s: usize| {
                    let o = offset(s) + 4 * j;
                    u64::from(u32::from_le_bytes([q[o], q[o + 1], q[o + 2], q[o + 3]]))
                };
                let (v0, v1, v2, v3) = (read(0), read(1), read(2), read(3));
                let u = v0 + v1;
                let w = v2 + v3;
                let x = v0 + P64 - v1;
                let y = v3 + P64 - v2;
                signed[0][j] = u + w;
                signed[1][j] = x + y;
                signed[2][j] = u + 2 * P64 - w;
                signed[3][j] = x + 2 * P64 - y;
            }
            for k in 0..4 {
                dots[which][k].push(circle[i][k], k_of(signed[k])).map_err(|_| Error::Parse)?;
            }
        }
    }
    let [d0, d1, d2] = dots;
    let finish = |d: [KbyKDot; 4]| {
        let [a, b, c, e] = d;
        [a.finish(), b.finish(), c.finish(), e.finish()]
    };
    Ok([finish(d0), finish(d1), finish(d2)])
}

/// E7: `accumulate_weights` with the residue rows updated in a fixed-size
/// loop. Same products, same fold after every fourth query, same final state.
#[inline(never)]
fn accumulate_weights_tight(p: &Prepared, a: &mut Accumulator, geometry: &QueryGeometry, weights: &mut BatchedWeights) -> Result<(), Error> {
    let raw: &mut [[u64; 4]; 64] = (&mut weights.raw[..]).try_into().map_err(|_| Error::Parse)?;
    for i in 0..QUERIES {
        let z = geometry.line_z[i - geometry.start];
        let mut node = z.mul(z).double().sub(M31::ONE);
        let mut basis = [M31::ONE; 64];
        let mut n = 1;
        while n < 64 {
            for j in 0..n {
                basis[n + j] = basis[j].mul(node);
            }
            node = node.mul(node).double().sub(M31::ONE);
            n *= 2;
        }
        let power = [u64::from(a.power.c0.a.0), u64::from(a.power.c0.b.0), u64::from(a.power.c1.a.0), u64::from(a.power.c1.b.0)];
        for j in 0..64 {
            let b = u64::from(basis[j].0);
            let row = &mut raw[j];
            row[0] += power[0] * b;
            row[1] += power[1] * b;
            row[2] += power[2] * b;
            row[3] += power[3] * b;
        }
        if weights.terms & 3 == 3 {
            for row in raw.iter_mut() {
                for limb in row {
                    *limb = (*limb & P64) + (*limb >> 31);
                }
            }
        }
        weights.terms += 1;
        a.power = a.power.mul(p.rho);
        a.next += 1;
    }
    Ok(())
}

/// Stage D certificate: six rounds of two WideExact values.
pub const CERTIFICATE_BYTES: usize = 6 * 2 * 32;
const ROW_CLAIMS: u8 = 33;
const ROW_ROUND: u8 = 34;

/// Stage D. Stage C with the relation pairing and the query check replaced by
/// one six-round sumcheck over the final message (design and status in the
/// note; UNPROVED PROTOCOL ADDITION).
#[inline(never)]
pub fn verify_with_certificate<H: Digest32>(public: Public<'_>, proof: &[u8], certificate: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    if certificate.len() != CERTIFICATE_BYTES {
        return Err(Error::Parse);
    }
    parse_shape(proof)?;
    canonical_scan(proof)?;
    mark(obs, Phase::Parsed);
    let mut g = [E::ZERO; 29];
    let p = prepare(public, proof, hash, obs, &mut g)?;
    mark(obs, Phase::Prepare);
    let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    batch_merkle(proof, &p, &folded_root, 0, hash)?;
    mark(obs, Phase::Merkle(0));
    batch_merkle(proof, &p, &folded_root, 1, hash)?;
    mark(obs, Phase::Merkle(SPLIT));
    let geometry = QueryGeometry::for_range(&p.queries, 0, QUERIES)?;
    let openings = &proof[compact::OFF_OPENINGS..compact::OFF_NODES];
    let sums = fold_sums(openings, &p.queries, p.rho, &p.alpha, &g, &geometry, Hook::of(obs))?;
    if sums.lhs1 != sums.rhs1 {
        return Err(Error::Query);
    }
    let v = relation_view(proof)?;
    let mut claim = finish_relation_round(v.round0, p.alpha[0], p.claim, 0)?;
    claim = finish_relation_round(v.round1, p.alpha[1], claim, 1)?;
    mark(obs, Phase::QueryPart(5, 0));
    final_sumcheck_checks(&p, v.final_message, claim, sums.rhs2, &geometry, certificate, hash, Hook::of(obs))?;
    mark(obs, Phase::Final);
    Ok(())
}

/// The two claims `sum_j f_j W_j = claim` and `sum_j f_j w_j = rhs2`, checked
/// through the certificate.
#[inline(never)]
fn final_sumcheck_checks<H: Digest32>(p: &Prepared, final_message: &[u8], claim: E, rhs2: E, geometry: &QueryGeometry, certificate: &[u8], hash: H, hook: Hook) -> Result<(), Error> {
    // The final sumcheck continues the opening transcript after rho; it does not start a new one.
    let mut t = Transcript::resume(hash, p.state);
    let lambda = t.scalar_k(ROW_CLAIMS, &claims_bytes(claim, rhs2));
    let (current, r) = final_rounds(&mut t, certificate, claim.add(rhs2.mul_qm31(lambda)))?;
    hook.note(Phase::QueryPart(5, 1));
    let (eq, digits) = equality_tables(&r);
    hook.note(Phase::QueryPart(5, 2));
    let f_at = final_message_at(final_message, &eq)?;
    hook.note(Phase::QueryPart(5, 3));
    let weights = Weights::new(p.variant, &p.semantic_alpha, &p.z)?;
    let w_at = weights.mle_at(&p.alpha[..2], p.kappa, &eq, &digits)?;
    hook.note(Phase::QueryPart(5, 4));
    #[cfg(feature = "final-pair-expansion")]
    let q_at = query_weight_mle_pairs(p, geometry, &r)?;
    #[cfg(not(feature = "final-pair-expansion"))]
    let q_at = query_weight_mle(p, geometry, &r)?;
    hook.note(Phase::QueryPart(5, 5));
    let combined = w_at.add(E::from_qm31(q_at.mul(lambda)));
    if f_at.mul(combined) != current {
        return Err(Error::Relation);
    }
    Ok(())
}

/// The six rounds of the final sumcheck: the running claim and the six challenges.
#[inline(always)]
fn final_rounds<H: Digest32>(t: &mut Transcript<H>, certificate: &[u8], start: E) -> Result<(E, [K; 6]), Error> {
    let mut current = start;
    let mut r = [K::ZERO; 6];
    for b in 0..6 {
        let bytes = &certificate[64 * b..64 * b + 64];
        let c0 = E::from_le_bytes(&bytes[..32]).ok_or(Error::Parse)?;
        let c2 = E::from_le_bytes(&bytes[32..]).ok_or(Error::Parse)?;
        r[b] = t.scalar_k(ROW_ROUND + b as u8, bytes);
        // s(0) + s(1) = 2 c0 + c1 + c2 is the running claim.
        let c1 = current.sub(c0).sub(c0).sub(c2);
        current = c0.add(c1.add(c2.mul_qm31(r[b])).mul_qm31(r[b]));
    }
    Ok((current, r))
}
#[inline(always)]
fn final_message_at(final_message: &[u8], eq: &[K; 64]) -> Result<E, Error> {
    let mut f_dot = EbyKDot::new();
    for j in 0..64 {
        match f_dot.push(field(final_message, j), eq[j]) { Ok(()) => {}, Err(_) => return Err(Error::Parse) }
    }
    Ok(f_dot.finish())
}

fn claims_bytes(claim: E, rhs2: E) -> [u8; 64] {
    let mut out = [0u8; 64];
    out[..32].copy_from_slice(&claim.to_le_bytes());
    out[32..].copy_from_slice(&rhs2.to_le_bytes());
    out
}

/// `eq[j] = prod_b (r_b if bit b of j else 1 - r_b)` for the 64 positions, and
/// the same products over the bit pairs (0,1), (2,3), (4,5).
#[inline(never)]
fn equality_tables(r: &[K; 6]) -> ([K; 64], [[K; 4]; 3]) {
    let mut eq = [K::ZERO; 64];
    eq[0] = K::ONE;
    let mut n = 1;
    for b in 0..6 {
        for j in 0..n {
            let high = eq[j].mul(r[b]);
            eq[j + n] = high;
            eq[j] = eq[j].sub(high);
        }
        n *= 2;
    }
    let digits = core::array::from_fn(|d| {
        let (a, b) = (r[2 * d], r[2 * d + 1]);
        let ab = a.mul(b);
        [K::ONE.sub(a).sub(b).add(ab), a.sub(ab), b.sub(ab), ab]
    });
    (eq, digits)
}

/// Extension at `r` of the query weight vector `w_j = sum_i rho^i b_j(x_i)`:
/// `b_j(x)` is the product over the set bits `b` of `j` of `t_b(x)`, with
/// `t_0` the query's node and `t_{b+1} = 2 t_b^2 - 1`, so the extension is
/// `sum_i rho^i prod_b (1 + r_b (t_b(x_i) - 1))`.
#[inline(never)]
fn query_weight_mle(p: &Prepared, geometry: &QueryGeometry, r: &[K; 6]) -> Result<K, Error> {
    let mut dot = KbyKDot::new();
    let mut power = K::ONE;
    for i in 0..QUERIES {
        let z = geometry.line_z[i - geometry.start];
        let mut node = z.mul(z).double().sub(M31::ONE);
        let mut product = K::ONE;
        for b in 0..6 {
            let factor = K::ONE.add(r[b].mul_m31(node.sub(M31::ONE)));
            product = if b == 0 { factor } else { product.mul(factor) };
            node = node.mul(node).double().sub(M31::ONE);
        }
        dot.push(power, product).map_err(|_| Error::Parse)?;
        power = power.mul(p.rho);
    }
    Ok(dot.finish())
}

/// D2: `query_weight_mle` with the six factors expanded in pairs,
/// `(1 + r_b a_b)(1 + r_{b+1} a_{b+1}) = 1 + r_b a_b + r_{b+1} a_{b+1} +
/// (r_b r_{b+1}) a_b a_{b+1}` with `a = t - 1` in the base field: per limb,
/// three products of canonical limbs (each below `2^62`) and one reduction.
#[inline(never)]
fn query_weight_mle_pairs(p: &Prepared, geometry: &QueryGeometry, r: &[K; 6]) -> Result<K, Error> {
    let limbs = |k: K| [u64::from(k.c0.a.0), u64::from(k.c0.b.0), u64::from(k.c1.a.0), u64::from(k.c1.b.0)];
    let pairs: [[[u64; 4]; 3]; 3] = core::array::from_fn(|q| [limbs(r[2 * q]), limbs(r[2 * q + 1]), limbs(r[2 * q].mul(r[2 * q + 1]))]);
    let mut dot = KbyKDot::new();
    let mut power = K::ONE;
    for i in 0..QUERIES {
        let z = geometry.line_z[i - geometry.start];
        let mut node = z.mul(z).double().sub(M31::ONE);
        let mut product = K::ONE;
        for q in 0..3 {
            let a0 = node.sub(M31::ONE);
            node = node.mul(node).double().sub(M31::ONE);
            let a1 = node.sub(M31::ONE);
            if q < 2 {
                node = node.mul(node).double().sub(M31::ONE);
            }
            let (x0, x1, x01) = (u64::from(a0.0), u64::from(a1.0), u64::from(a0.mul(a1).0));
            let [l0, l1, l01] = &pairs[q];
            let factor = k_of([
                1 + l0[0] * x0 + l1[0] * x1 + l01[0] * x01,
                l0[1] * x0 + l1[1] * x1 + l01[1] * x01,
                l0[2] * x0 + l1[2] * x1 + l01[2] * x01,
                l0[3] * x0 + l1[3] * x1 + l01[3] * x01,
            ]);
            product = if q == 0 { factor } else { product.mul(factor) };
        }
        dot.push(power, product).map_err(|_| Error::Parse)?;
        power = power.mul(p.rho);
    }
    Ok(dot.finish())
}

/// The explicit 64-entry vectors of stage D for an accepting-shape proof:
/// `(claim, rhs2, f, W, w)`. Host and test use only.
#[cfg(any(test, feature = "prover"))]
#[allow(clippy::type_complexity)]
fn final_sumcheck_vectors<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H) -> Result<(Box<Prepared>, E, E, Vec<E>, Vec<E>, Vec<K>), Error> {
    parse_shape(proof)?;
    canonical_scan(proof)?;
    let mut g = [E::ZERO; 29];
    let p = prepare(public, proof, hash, None, &mut g)?;
    let geometry = QueryGeometry::for_range(&p.queries, 0, QUERIES)?;
    let openings = &proof[compact::OFF_OPENINGS..compact::OFF_NODES];
    let sums = fold_sums(openings, &p.queries, p.rho, &p.alpha, &g, &geometry, Hook::NONE)?;
    let v = relation_view(proof)?;
    let mut claim = finish_relation_round(v.round0, p.alpha[0], p.claim, 0)?;
    claim = finish_relation_round(v.round1, p.alpha[1], claim, 1)?;
    let weights = Weights::new(p.variant, &p.semantic_alpha, &p.z)?;
    let kp = powers::<7>(p.kappa);
    let f: Vec<E> = (0..64).map(|j| field(v.final_message, j)).collect();
    let relation: Vec<E> = (0..64)
        .map(|j| (0..7).fold(E::ZERO, |w, kind| w.add(kp[kind].mul(weights.dual_raw(kind, j, &p.alpha[..2])))))
        .collect();
    let mut a = Accumulator::new(Variant::S2)?;
    let mut pending = BatchedWeights::new(&a.weights)?;
    accumulate_weights(&p, &mut a, &geometry, &mut pending);
    pending.finish(&mut a.weights);
    Ok((p, claim, sums.rhs2, f, relation, a.weights))
}

/// Honest sumcheck prover for `sum_j f_j u_j` with `u = W + lambda w`, on the
/// transcript the verifier uses, given the claims the verifier will bind.
#[cfg(any(test, feature = "prover"))]
fn final_sumcheck_rounds<H: Digest32>(p: &Prepared, claim: E, rhs2: E, mut f: Vec<E>, relation: &[E], query: &[K], hash: H) -> Vec<u8> {
    // The final sumcheck continues the opening transcript after rho; it does not start a new one.
    let mut t = Transcript::resume(hash, p.state);
    let lambda = t.scalar_k(ROW_CLAIMS, &claims_bytes(claim, rhs2));
    let mut u: Vec<E> = (0..64).map(|j| relation[j].add(E::from_qm31(query[j].mul(lambda)))).collect();
    let half = M31(1 << 30);
    let mut out = Vec::new();
    for b in 0..6 {
        let n = f.len() / 2;
        let (mut s0, mut s1, mut s2) = (E::ZERO, E::ZERO, E::ZERO);
        for m in 0..n {
            s0 = s0.add(f[2 * m].mul(u[2 * m]));
            s1 = s1.add(f[2 * m + 1].mul(u[2 * m + 1]));
            s2 = s2.add(f[2 * m + 1].add(f[2 * m + 1]).sub(f[2 * m]).mul(u[2 * m + 1].add(u[2 * m + 1]).sub(u[2 * m])));
        }
        let c2 = s2.sub(s1).sub(s1).add(s0).mul_m31(half);
        out.extend_from_slice(&s0.to_le_bytes());
        out.extend_from_slice(&c2.to_le_bytes());
        let r = t.scalar_k(ROW_ROUND + b as u8, &out[64 * b..64 * b + 64]);
        f = (0..n).map(|m| f[2 * m].add(f[2 * m + 1].sub(f[2 * m]).mul_qm31(r))).collect();
        u = (0..n).map(|m| u[2 * m].add(u[2 * m + 1].sub(u[2 * m]).mul_qm31(r))).collect();
    }
    out
}

/// The honest stage D certificate of a proof. It is a function of public
/// proof data only (no witness).
#[cfg(any(test, feature = "prover"))]
pub fn final_message_certificate<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H) -> Result<Vec<u8>, Error> {
    let (p, claim, rhs2, f, relation, query) = final_sumcheck_vectors(public, proof, hash)?;
    Ok(final_sumcheck_rounds(&p, claim, rhs2, f, &relation, &query, hash))
}

/// The Aspis proof format. The two-transaction verifier's compact
/// layout up to the end of the 22 openings (same offsets), then one multiproof
/// per tree over all 22 queries in a fixed zero-padded slot, then the final-sumcheck
/// certificate. Design, slot bounds and status: ONE-TX-EXPERIMENT.md.
pub mod format {
    use crate::compact;
    /// "ASPIS", two reserved zero bytes, proof format number 2 (the one-transaction
    /// format whose final sumcheck continues the opening transcript). The devnet
    /// verifier deployed on 2026-11-11 (source 8a4059c8bc2) used the experiment's
    /// earlier magic `R1F1SM22` and a fresh transcript start for the final sumcheck;
    /// its proofs are not valid here and these are not valid there.
    pub const MAGIC: &[u8; 8] = b"ASPIS\x00\x00\x02";
    /// Worst-case supplied nodes: C1, C2 (22 leaves at depth 18) and the
    /// folded tree (at most 22 leaves below 2^16 at depth 18).
    pub const SLOT_NODES: [usize; 3] = [296, 296, 254];
    pub const OFF_NODES: usize = compact::OFF_NODES;
    pub const fn slot_offset(slot: usize) -> usize {
        let mut at = OFF_NODES;
        let mut i = 0;
        while i < slot {
            at += 32 * SLOT_NODES[i];
            i += 1;
        }
        at
    }
    pub const OFF_CERTIFICATE: usize = slot_offset(3);
    pub const PROOF_BYTES: usize = OFF_CERTIFICATE + super::CERTIFICATE_BYTES;
    const _: () = assert!(PROOF_BYTES == 55_815);
}

/// Shape of an Aspis-format proof: fixed length, magic, variant S2, zero
/// header tail.
#[inline(never)]
pub fn parse_packed_shape(proof: &[u8]) -> Result<(), Error> {
    if proof.len() != format::PROOF_BYTES
        || &proof[..8] != format::MAGIC
        || proof[8] != Variant::S2.tag()
        || proof[9..16].iter().any(|&x| x != 0)
    {
        return Err(Error::Parse);
    }
    Ok(())
}

/// Query keys `(index << 8) | position`, sorted by index.
#[inline(always)]
fn merged_keys(queries: &[u32; 22], folded: bool) -> [u64; 22] {
    let mut keys = [0u64; 22];
    for j in 0..22 {
        let index = if folded { queries[j] / 4 } else { queries[j] };
        keys[j] = (u64::from(index) << 8u32) | j as u64;
    }
    for i in 1..22 {
        let mut j = i;
        while j > 0 && keys[j - 1] > keys[j] {
            keys.swap(j - 1, j);
            j -= 1;
        }
    }
    keys
}

/// One merged multiproof: the leaves of `tree` in key order (equal folded
/// indices must carry identical leaves and are merged, as in the pinned
/// batches), then the single-pass in-place traversal over the tree's slot.
#[inline(always)]
fn merged_tree<H: Digest32>(proof: &[u8], keys: &[u64; 22], root: &[u8; 32], tree: usize, hash: H) -> Result<(), Error> {
    let mut idx = [0u32; multiproof::MAX_MERGED];
    let mut val = [[0u8; 32]; multiproof::MAX_MERGED];
    let mut d = 0;
    for &key in keys {
        let index = (key >> 8u32) as u32;
        let leaf = batch_leaf(hash, tree, opening(proof, (key & 0xff) as usize));
        if d > 0 && idx[d - 1] == index {
            if val[d - 1] != leaf {
                return Err(Error::Merkle);
            }
            continue;
        }
        idx[d] = index;
        val[d] = leaf;
        d += 1;
    }
    let nodes = &proof[format::slot_offset(tree)..format::slot_offset(tree + 1)];
    merkle_verdict(multiproof::verify_counting_merged(hash, root, &mut idx, &mut val, d, nodes), nodes)
}

/// The three merged multiproofs. C1 and C2 are opened at the same indices and
/// share one sorted schedule.
#[inline(never)]
fn merged_merkle<H: Digest32>(proof: &[u8], p: &Prepared, folded_root: &[u8; 32], hash: H) -> Result<(), Error> {
    let keys = merged_keys(&p.queries, false);
    merged_tree(proof, &keys, &p.roots[0], 0, hash)?;
    merged_tree(proof, &keys, &p.roots[1], 1, hash)?;
    let keys = merged_keys(&p.queries, true);
    merged_tree(proof, &keys, folded_root, 2, hash)
}

/// The one-transaction verifier: one invocation, the batched first-fold check,
/// the final sumcheck with its certificate carried in the proof, one multiproof per tree.
/// UNPROVED (see `SOUNDNESS-ROWS.md` and `ASPIS-FREEZE.md`).
#[inline(never)]
fn verify_hooked<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H, hook: Hook) -> Result<(), Error> {
    parse_packed_shape(proof)?;
    canonical_scan(proof)?;
    hook.note(Phase::Parsed);
    let mut g = [E::ZERO; 29];
    let p = prepare_packed(public, proof, hash, hook, &mut g)?;
    hook.note(Phase::Prepare);
    let geometry = QueryGeometry::for_range(&p.queries, 0, QUERIES)?;
    let openings = &proof[compact::OFF_OPENINGS..compact::OFF_NODES];
    let sums = fold_sums(openings, &p.queries, p.rho, &p.alpha, &g, &geometry, hook)?;
    if sums.lhs1 != sums.rhs1 {
        return Err(Error::Query);
    }
    let v = relation_view(proof)?;
    let mut claim = finish_relation_round(v.round0, p.alpha[0], p.claim, 0)?;
    claim = finish_relation_round(v.round1, p.alpha[1], claim, 1)?;
    hook.note(Phase::QueryPart(5, 0));
    final_sumcheck_checks(&p, v.final_message, claim, sums.rhs2, &geometry, &proof[format::OFF_CERTIFICATE..], hash, hook)?;
    hook.note(Phase::Final);
    // Merkle authentication LAST: every transcript row (0 to 39) is derived before any Merkle
    // digest is computed, which is the order the formal model has (all rows, then the terminal
    // decision). The same checks are made and all must pass, so acceptance is unchanged; only
    // the order of rejections differs. The opened values the earlier steps used are the ones
    // authenticated here.
    let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    merged_merkle(proof, &p, &folded_root, hash)?;
    hook.note(Phase::Merkle(0));
    Ok(())
}

/// The entry with an observer, as before (tests, tools, profiling builds). Without `phase-observer` the
/// observer is ignored.
#[inline(always)]
pub fn verify<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    verify_hooked(public, proof, hash, Hook::of(obs))
}

/// The on-chain entry of the Aspis one-transaction verifier: no observer parameter.
#[inline(always)]
pub fn verify_unobserved<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H) -> Result<(), Error> {
    verify_hooked(public, proof, hash, Hook::NONE)
}

/// `candidate::prepare` for the one-transaction path (new gate): the same steps in the same order, with the
/// semantic layer entered through `verify_unobserved` unless a profiling build asks for the observer.
#[inline(never)]
fn prepare_packed<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H, hook: Hook, g: &mut [E; 29]) -> Result<Box<Prepared>, Error> {
    let mut logical = aspis_core::r0::heap::filled(compact::LOGICAL_SEMANTIC + compact::LOGICAL_Y1, 0u8).map_err(|_| Error::Allocation)?;
    let (semantic, y1) = logical.split_at_mut(compact::LOGICAL_SEMANTIC);
    compact::expand_semantic(&proof[compact::OFF_SEMANTIC..compact::OFF_Y1], semantic)?;
    compact::expand_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE], y1)?;
    let v = wide_view(proof, &logical[..compact::LOGICAL_SEMANTIC], &logical[compact::LOGICAL_SEMANTIC..])?;
    #[cfg(feature = "phase-observer")]
    let sem = crate::r1_semantic::verify_observed(public, v.semantic, hash, hook.0).map_err(|_| Error::Semantic)?;
    #[cfg(not(feature = "phase-observer"))]
    let sem = crate::r1_semantic::verify_unobserved(public, v.semantic, hash).map_err(|_| Error::Semantic)?;
    hook.note(Phase::Semantic);
    Prepared::new(&sem, &v, hash, g)
}

/// The supplied sibling positions of a binary multiproof over the strictly
/// increasing `indices`, as `(level, index)` in the canonical stream order
/// (level 0 is the leaves).
#[cfg(any(test, feature = "prover"))]
fn supplied_positions(indices: &[u32]) -> Vec<(u32, u32)> {
    let mut out = Vec::new();
    let mut level: Vec<u32> = indices.to_vec();
    for depth in 0..multiproof::LEAF_BITS {
        let mut next = Vec::new();
        let mut i = 0;
        while i < level.len() {
            if i + 1 < level.len() && level[i + 1] == level[i] ^ 1 {
                i += 2;
            } else {
                out.push((depth, level[i] ^ 1));
                i += 1;
            }
            next.push(level[i - 1] >> 1);
        }
        level = next;
    }
    out
}

#[cfg(any(test, feature = "prover"))]
fn distinct_sorted(queries: &[u32], folded: bool) -> Vec<u32> {
    let mut out: Vec<u32> = queries.iter().map(|&u| if folded { u / 4 } else { u }).collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// Re-pack a two-transaction compact proof into the Aspis format. A function of the
/// proof and the public statement only: each merged multiproof's nodes are
/// among the two batches' supplied nodes (a sibling the merged traversal needs
/// is unoccupied by every query, so the batch holding its occupied sibling
/// supplied it), and the certificate is the honest final-sumcheck certificate. This
/// is also the prover's publish step for the Aspis format.
#[cfg(any(test, feature = "prover"))]
pub fn pack<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H) -> Result<Vec<u8>, Error> {
    let (p, claim, rhs2, f, relation, query) = final_sumcheck_vectors(public, proof, hash)?;
    let certificate = final_sumcheck_rounds(&p, claim, rhs2, f, &relation, &query, hash);
    let mut out = Vec::with_capacity(format::PROOF_BYTES);
    out.extend_from_slice(&proof[..compact::OFF_NODES]);
    out[..8].copy_from_slice(format::MAGIC);
    for tree in 0..3 {
        let mut known: Vec<((u32, u32), [u8; 32])> = Vec::new();
        for batch in 0..2 {
            let (lo, hi) = if batch == 0 { (0, SPLIT) } else { (SPLIT, 22) };
            let positions = supplied_positions(&distinct_sorted(&p.queries[lo..hi], tree == 2));
            let nodes = slot(proof, 3 * batch + tree);
            if 32 * positions.len() > nodes.len() {
                return Err(Error::Merkle);
            }
            for (k, position) in positions.into_iter().enumerate() {
                known.push((position, nodes[32 * k..32 * k + 32].try_into().unwrap()));
            }
        }
        let merged = supplied_positions(&distinct_sorted(&p.queries, tree == 2));
        if merged.len() > format::SLOT_NODES[tree] {
            return Err(Error::Merkle);
        }
        for position in &merged {
            let node = known.iter().find(|(at, _)| at == position).ok_or(Error::Merkle)?;
            out.extend_from_slice(&node.1);
        }
        out.resize(format::slot_offset(tree + 1), 0);
    }
    out.extend_from_slice(&certificate);
    if out.len() != format::PROOF_BYTES {
        return Err(Error::Parse);
    }
    Ok(out)
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
            let actual = fold_sums(&openings, &queries, rho, &alpha, &g, &geometry, Hook::NONE).unwrap();
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
            assert_eq!(fold_sums(&openings, &queries, rho, &[max_e, max_e], &g, &geometry, Hook::NONE).unwrap(), expected);
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
            verify_unbatched(statement.semantic_public(), proof, Sha, None).unwrap_or_else(|e| panic!("{name} fused {e:?}"));
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
            assert!(verify_unbatched(statement.semantic_public(), &bad, Sha, None).is_err(), "fused accepted a mutation at {at}");
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
        let honest = fold_sums(&openings, &p.queries, p.rho, &p.alpha, &g, &geometry, Hook::NONE).unwrap();
        assert_eq!(honest.lhs1, honest.rhs1);
        for query in [0usize, 9, 10, 21] {
            // One base lane, the C1 tail lane, one C2 lane, in each slot.
            for at in (0..4).flat_map(|s| [s * 120 + 4 * (query % 26), s * 120 + 104, 480 + s * 32 + 16]) {
                let mut bad = openings.clone();
                let b = &mut bad[query * OPENING + at];
                *b = if *b == 0 { 1 } else { *b - 1 }; // stays canonical
                let sums = fold_sums(&bad, &p.queries, p.rho, &p.alpha, &g, &geometry, Hook::NONE).unwrap();
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
        let sums = fold_sums(&openings, &p.queries, p.rho, &p.alpha, &g, &geometry, Hook::NONE).unwrap();
        assert_eq!(sums.lhs1, sums.rhs1, "the crafted residuals cancel at rho");
        let (_, first, authenticated) = reference(&openings, &p.queries, p.rho, &p.alpha, &g, &geometry);
        assert_ne!(first[3], authenticated[3]);
        assert_ne!(first[4], authenticated[4]);
        // At any other challenge the same data is rejected.
        let other = p.rho.add(K::ONE);
        let moved = fold_sums(&openings, &p.queries, other, &p.alpha, &g, &geometry, Hook::NONE).unwrap();
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

    /// E3: on every validated semantic row of every fixture, the decoder
    /// returns what the checked QM31 decoder returns on the same bytes. With
    /// `validated-decode` off this compares the pinned decoder with
    /// itself; with it on, the direct limb load with the pinned decoder.
    #[test]
    fn validated_decode_equals_the_checked_decoder_on_every_semantic_row() {
        for (name, proof, _) in FIXTURES {
            let mut logical = vec![0u8; compact::LOGICAL_SEMANTIC];
            compact::expand_semantic(&proof[compact::OFF_SEMANTIC..compact::OFF_Y1], &mut logical).unwrap();
            let prefix = crate::r1_wire::Prefix::parse(&logical).unwrap();
            let mut values = 0;
            for row in 14u8..=26 {
                let record = prefix.validated_record(row).unwrap();
                let payload = record.payload();
                for j in 0..payload.len() / 32 {
                    assert_eq!(record.decode_k::<1>(j).unwrap()[0], K::from_le_bytes(&payload[32 * j..32 * j + 16]).unwrap(), "{name} row {row} value {j}");
                    values += 1;
                }
            }
            assert_eq!(values, compact::SEMANTIC_COMPACT_VALUES);
        }
    }

    #[test]
    fn tight_lane_kernels_equal_the_first_kernels_on_arbitrary_and_edge_inputs() {
        let mut state = 0x0123_4567_89ab_cdefu64;
        for case in 0..30 {
            let queries = distinct_queries(&mut state);
            let geometry = QueryGeometry::for_range(&queries, 0, 22).unwrap();
            let openings = random_openings(&mut state, case % 5);
            let rho = random_k(&mut state, if case < 4 { case } else { 3 });
            let c = coefficients(rho, &geometry).unwrap();
            let tight = base_lanes_tight(&openings, &c.circle).unwrap();
            for lane in 0..26 {
                assert_eq!(tight[lane], base_lane(&openings, &c.circle, lane), "case {case} lane {lane}");
            }
            let tight = extension_lanes_tight(&openings, &c.circle).unwrap();
            for which in 0..3 {
                assert_eq!(tight[which], extension_lane(&openings, &c.circle, which).unwrap(), "case {case} lane {which}");
            }
        }
        // Maximal limbs everywhere: values, and coefficients forced to P - 1.
        let queries = distinct_queries(&mut state);
        let geometry = QueryGeometry::for_range(&queries, 0, 22).unwrap();
        let openings = random_openings(&mut state, 2);
        let top = random_k(&mut state, 2);
        let circle = vec![[top; 4]; QUERIES];
        let tight = base_lanes_tight(&openings, &circle).unwrap();
        for lane in 0..26 {
            assert_eq!(tight[lane], base_lane(&openings, &circle, lane));
        }
        let tight = extension_lanes_tight(&openings, &circle).unwrap();
        for which in 0..3 {
            assert_eq!(tight[which], extension_lane(&openings, &circle, which).unwrap());
        }
        let _ = geometry;
    }

    /// `scanned_k` is `K::from_le_bytes` on canonical limbs (the scan's precondition), at every
    /// extension-lane offset of random and edge openings.
    #[test]
    fn scanned_extension_values_equal_the_checked_decoder_on_canonical_openings() {
        let mut state = 0x7766_5544_3322_1100u64;
        for case in 0..12 {
            let openings = random_openings(&mut state, case % 5);
            for i in 0..QUERIES {
                let q: &[u8; 608] = openings[i * OPENING..i * OPENING + 608].try_into().unwrap();
                for which in 0..3 {
                    for s in 0..4 {
                        let at = if which == 2 { s * 120 + 104 } else { 480 + s * 32 + which * 16 };
                        assert_eq!(scanned_k(q, at), K::from_le_bytes(&q[at..at + 16]).unwrap(), "case {case} query {i} lane {which} slot {s}");
                    }
                }
            }
        }
    }

    #[test]
    fn tight_weight_accumulation_equals_the_first_form() {
        for (name, proof, public) in FIXTURES {
            let (p, _) = prepared(proof, public);
            let geometry = QueryGeometry::for_range(&p.queries, 0, 22).unwrap();
            let run = |tight: bool| {
                let mut a = Accumulator::new(Variant::S2).unwrap();
                let mut pending = BatchedWeights::new(&a.weights).unwrap();
                if tight {
                    accumulate_weights_tight(&p, &mut a, &geometry, &mut pending).unwrap();
                } else {
                    accumulate_weights(&p, &mut a, &geometry, &mut pending);
                }
                pending.finish(&mut a.weights);
                (a.weights, a.power, a.next, pending.terms)
            };
            assert_eq!(run(true), run(false), "{name}");
        }
    }

    /// E4a: the single-pass tail returns the same result as the two-pass
    /// tail, error kind included, on every slot of every fixture and under a
    /// changed node, changed padding, both, and a slot too short for the set.
    #[test]
    fn single_pass_merkle_tail_equals_the_two_pass_tail() {
        let mut compared = 0;
        for (name, proof, public) in FIXTURES {
            let (p, _) = prepared(proof, public);
            let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
            let roots = [p.roots[0], p.roots[1], folded_root];
            for batch in 0..2 {
                for tree in 0..3 {
                    let (lo, hi) = if batch == 0 { (0, SPLIT) } else { (SPLIT, 22) };
                    let n = hi - lo;
                    let keys = sort_batch_keys(batch_keys(&p.queries, lo, n, tree), n);
                    let mut idx = [0u32; multiproof::MAX_BATCH];
                    let mut val = [[0u8; 32]; multiproof::MAX_BATCH];
                    let mut d = 0;
                    for position in 0..n {
                        let key = keys[position];
                        let index = (key >> 8u32) as u32;
                        let leaf = batch_leaf(Sha, tree, opening(proof, lo + (key & 0xff) as usize));
                        if d > 0 && idx[d - 1] == index {
                            continue;
                        }
                        idx[d] = index;
                        val[d] = leaf;
                        d += 1;
                    }
                    let nodes = slot(proof, 3 * batch + tree).to_vec();
                    let count = multiproof::node_count(Arity::Two, &idx[..d]).unwrap();
                    let mut variants = vec![nodes.clone()];
                    let mut node_changed = nodes.clone();
                    node_changed[32 * (count / 2) + 5] ^= 1;
                    variants.push(node_changed.clone());
                    if 32 * count < nodes.len() {
                        let mut padding = nodes.clone();
                        padding[32 * count + 9] ^= 0x80;
                        variants.push(padding);
                        node_changed[nodes.len() - 1] ^= 1;
                        variants.push(node_changed);
                    }
                    variants.push(nodes[..32 * (count - 1)].to_vec());
                    variants.push(nodes[..32 * count].to_vec());
                    for (v, bytes) in variants.iter().enumerate() {
                        let (mut i1, mut v1, mut i2, mut v2) = (idx, val, idx, val);
                        let two = merkle_tail_two_pass(Sha, &roots[tree], &mut i1, &mut v1, d, bytes);
                        let one = merkle_tail_single_pass(Sha, &roots[tree], &mut i2, &mut v2, d, bytes);
                        assert_eq!(one, two, "{name} batch {batch} tree {tree} variant {v}");
                        let (mut i3, mut v3, mut i4, mut v4) = (idx, val, idx, val);
                        let counting = merkle_verdict(multiproof::verify_counting(Sha, &roots[tree], &mut i3, &mut v3, d, bytes), bytes);
                        let direct = merkle_verdict(multiproof::verify_counting_direct(Sha, &roots[tree], &mut i4, &mut v4, d, bytes), bytes);
                        assert_eq!(counting, two, "{name} batch {batch} tree {tree} variant {v} counting");
                        assert_eq!(direct, two, "{name} batch {batch} tree {tree} variant {v} direct");
                        if v == 0 {
                            assert_eq!(two, Ok(()), "{name} batch {batch} tree {tree}");
                        }
                        compared += 1;
                    }
                }
            }
            // A malformed index set (not strictly increasing).
            let mut idx = [0u32; multiproof::MAX_BATCH];
            idx[0] = 7;
            idx[1] = 7;
            let (mut i2, mut v1, mut v2) = (idx, [[0u8; 32]; multiproof::MAX_BATCH], [[0u8; 32]; multiproof::MAX_BATCH]);
            let nodes = slot(proof, 0);
            assert_eq!(merkle_tail_single_pass(Sha, &roots[0], &mut i2, &mut v2, 2, nodes), merkle_tail_two_pass(Sha, &roots[0], &mut idx, &mut v1, 2, nodes));
        }
        assert!(compared >= 6 * 6 * 5);
    }

    fn eq_of(r: &[K; 6]) -> ([K; 64], [[K; 4]; 3]) {
        equality_tables(r)
    }

    #[test]
    fn final_sumcheck_extensions_equal_the_direct_sums_over_the_explicit_vectors() {
        let mut state = 0x1357_9bdf_0246_8aceu64;
        for (name, proof, public) in FIXTURES {
            let statement = decode(public);
            let (p, claim, rhs2, f, relation, query) = final_sumcheck_vectors(statement.semantic_public(), proof, Sha).unwrap();
            let weights = Weights::new(p.variant, &p.semantic_alpha, &p.z).unwrap();
            let final_message = &proof[compact::OFF_FINAL..compact::OFF_OPENINGS];
            // The explicit vectors reproduce the two pinned inner products.
            let pair = weights.pair(&p.alpha[..2], final_message, p.kappa).unwrap();
            assert_eq!((0..64).fold(E::ZERO, |a, j| a.add(f[j].mul(relation[j]))), pair, "{name}");
            assert_eq!(pair, claim, "{name}");
            assert_eq!((0..64).fold(E::ZERO, |a, j| a.add(f[j].mul_qm31(query[j]))), rhs2, "{name}");
            let geometry = QueryGeometry::for_range(&p.queries, 0, 22).unwrap();
            for case in 0..8 {
                let r: [K; 6] = core::array::from_fn(|b| match case {
                    0 => K::ZERO,
                    1 => K::ONE,
                    2 => if b % 2 == 0 { K::ONE } else { K::ZERO },
                    _ => random_k(&mut state, 3),
                });
                let (eq, digits) = eq_of(&r);
                // The table is the equality polynomial: on Boolean points it selects one index.
                if case < 3 {
                    let index: usize = (0..6).map(|b| if r[b] == K::ONE { 1 << b } else { 0 }).sum();
                    for j in 0..64 {
                        assert_eq!(eq[j], if j == index { K::ONE } else { K::ZERO });
                    }
                }
                let direct = (0..64).fold(E::ZERO, |a, j| a.add(relation[j].mul_qm31(eq[j])));
                assert_eq!(weights.mle_at(&p.alpha[..2], p.kappa, &eq, &digits).unwrap(), direct, "{name} case {case}");
                let direct = (0..64).fold(K::ZERO, |a, j| a.add(query[j].mul(eq[j])));
                assert_eq!(query_weight_mle(&p, &geometry, &r).unwrap(), direct, "{name} case {case}");
                assert_eq!(query_weight_mle_pairs(&p, &geometry, &r).unwrap(), direct, "{name} pairs case {case}");
                if case == 3 {
                    // Maximal limbs in the challenge.
                    let top = random_k(&mut state, 2);
                    let r = [top; 6];
                    assert_eq!(query_weight_mle_pairs(&p, &geometry, &r).unwrap(), query_weight_mle(&p, &geometry, &r).unwrap());
                }
            }
        }
    }

    #[test]
    fn final_sumcheck_accepts_the_six_fixtures_and_rejects_every_certificate_byte_change() {
        for (index, (name, proof, public)) in FIXTURES.into_iter().enumerate() {
            let statement = decode(public);
            let certificate = final_message_certificate(statement.semantic_public(), proof, Sha).unwrap();
            assert_eq!(certificate.len(), CERTIFICATE_BYTES);
            verify_with_certificate(statement.semantic_public(), proof, &certificate, Sha, None).unwrap_or_else(|e| panic!("{name} summed {e:?}"));
            // Another proof's certificate, and wrong lengths.
            let (_, other_proof, other_public) = FIXTURES[(index + 1) % 6];
            let other = final_message_certificate(decode(other_public).semantic_public(), other_proof, Sha).unwrap();
            assert!(verify_with_certificate(statement.semantic_public(), proof, &other, Sha, None).is_err());
            assert!(verify_with_certificate(statement.semantic_public(), proof, &certificate[..CERTIFICATE_BYTES - 1], Sha, None).is_err());
            assert!(verify_with_certificate(statement.semantic_public(), proof, &[], Sha, None).is_err());
            if index == 0 {
                // The final checks alone, so that all 384 positions are cheap to try.
                let (p, claim, rhs2, _, _, _) = final_sumcheck_vectors(statement.semantic_public(), proof, Sha).unwrap();
                let geometry = QueryGeometry::for_range(&p.queries, 0, 22).unwrap();
                let final_message = &proof[compact::OFF_FINAL..compact::OFF_OPENINGS];
                final_sumcheck_checks(&p, final_message, claim, rhs2, &geometry, &certificate, Sha, Hook::NONE).unwrap();
                for at in 0..CERTIFICATE_BYTES {
                    for bit in [1u8, 0x80] {
                        let mut bad = certificate.clone();
                        bad[at] ^= bit;
                        assert!(final_sumcheck_checks(&p, final_message, claim, rhs2, &geometry, &bad, Sha, Hook::NONE).is_err(), "byte {at} bit {bit}");
                    }
                }
            }
            // The 20 proof mutations are still rejected with the honest certificate of the unmutated proof.
            if index == 0 {
                for at in mutation_offsets() {
                    let mut bad = proof.to_vec();
                    bad[at] ^= 1;
                    assert!(verify_with_certificate(statement.semantic_public(), &bad, &certificate, Sha, None).is_err(), "mutation at {at}");
                }
            }
        }
    }

    /// TEETH: a prover who follows the protocol honestly but for a false
    /// claim is rejected, whichever of the two claims is false and whether
    /// the false claim or the true sum is what it binds in the transcript.
    #[test]
    fn final_sumcheck_rejects_honest_rounds_for_a_false_relation_or_query_claim() {
        let (_, proof, public) = FIXTURES[4];
        let statement = decode(public);
        let (p, claim, rhs2, f, relation, query) = final_sumcheck_vectors(statement.semantic_public(), proof, Sha).unwrap();
        let geometry = QueryGeometry::for_range(&p.queries, 0, 22).unwrap();
        let final_message = &proof[compact::OFF_FINAL..compact::OFF_OPENINGS];
        let one = E::from_qm31(K::ONE);
        for (false_claim, false_rhs2) in [(claim.add(one), rhs2), (claim, rhs2.add(one)), (claim.add(one), rhs2.sub(one))] {
            // Rounds computed for the true vectors on the transcript of the false claims.
            let adaptive = final_sumcheck_rounds(&p, false_claim, false_rhs2, f.clone(), &relation, &query, Sha);
            assert!(final_sumcheck_checks(&p, final_message, false_claim, false_rhs2, &geometry, &adaptive, Sha, Hook::NONE).is_err());
            // Rounds computed for the true claims, presented against the false ones.
            let honest = final_sumcheck_rounds(&p, claim, rhs2, f.clone(), &relation, &query, Sha);
            assert!(final_sumcheck_checks(&p, final_message, false_claim, false_rhs2, &geometry, &honest, Sha, Hook::NONE).is_err());
        }
        // A false weight vector with a true-looking claim: the rounds are honest for
        // a perturbed relation vector whose sum the prover claims.
        let mut wrong = relation.clone();
        wrong[17] = wrong[17].add(one);
        let wrong_claim = (0..64).fold(E::ZERO, |a, j| a.add(f[j].mul(wrong[j])));
        let rounds = final_sumcheck_rounds(&p, wrong_claim, rhs2, f.clone(), &wrong, &query, Sha);
        assert!(final_sumcheck_checks(&p, final_message, wrong_claim, rhs2, &geometry, &rounds, Sha, Hook::NONE).is_err());
        // Control: the true claims with honest rounds are accepted.
        let honest = final_sumcheck_rounds(&p, claim, rhs2, f, &relation, &query, Sha);
        final_sumcheck_checks(&p, final_message, claim, rhs2, &geometry, &honest, Sha, Hook::NONE).unwrap();
    }

    /// G3: the word-wise scan and the pinned scan agree on the fixtures and
    /// under every tested bad limb value at positions in every scanned region
    /// and in the regions the scan must ignore (salts and Merkle nodes).
    #[test]
    fn word_scan_equals_the_pinned_scan() {
        let (_, proof, _) = FIXTURES[5];
        assert_eq!(canonical_scan_words(proof), Ok(()));
        assert_eq!(canonical_scan_pinned(proof), Ok(()));
        let o = compact::OFF_OPENINGS;
        let mut positions = vec![compact::OFF_Y1, compact::OFF_Y1 + 12, compact::OFF_INACTIVE - 4, compact::OFF_INACTIVE, compact::OFF_INACTIVE + 28,
            compact::OFF_ROUND0, compact::OFF_ROUND0 + 220, compact::OFF_ROUND1, compact::OFF_FINAL, compact::OFF_FINAL + 4, compact::OFF_OPENINGS - 4,
            compact::OFF_SEMANTIC + 40, compact::OFF_FOLDED_ROOT, compact::OFF_FOLDED_ROOT + 28, compact::OFF_NODES, compact::OFF_NODES + 100];
        for i in [0usize, 7, 21] {
            for at in [0usize, 4, 100, 104, 116, 120, 476, 480, 492, 604, 608, 636, 668, 672, 700, 796, 800, 828] {
                positions.push(o + i * OPENING + at);
            }
        }
        let mut rejected = 0;
        for at in positions {
            for bad in [aspis_core::field::P, aspis_core::field::P + 1, 1u32 << 31, u32::MAX, 0, aspis_core::field::P - 1] {
                let mut changed = proof.to_vec();
                changed[at..at + 4].copy_from_slice(&bad.to_le_bytes());
                let pinned = canonical_scan_pinned(&changed);
                assert_eq!(canonical_scan_words(&changed), pinned, "offset {at} value {bad}");
                rejected += pinned.is_err() as usize;
            }
        }
        assert!(rejected > 100);
    }

    fn packed_fixture(index: usize) -> (Vec<u8>, &'static [u8]) {
        let (_, proof, public) = FIXTURES[index];
        (pack(decode(public).semantic_public(), proof, Sha).unwrap(), public)
    }

    #[test]
    fn packed_format_accepts_the_six_repacked_fixtures_and_the_two_formats_reject_each_other() {
        for index in 0..6 {
            let (name, proof, public) = FIXTURES[index];
            let (packed, _) = packed_fixture(index);
            assert_eq!(packed.len(), format::PROOF_BYTES);
            let statement = decode(public);
            verify(statement.semantic_public(), &packed, Sha, None).unwrap_or_else(|e| panic!("{name} summed format {e:?}"));
            // The pinned proof is not a summed-format proof, and the reverse.
            assert_eq!(verify(statement.semantic_public(), proof, Sha, None), Err(Error::Parse));
            assert!(tx1(statement.semantic_public(), public, &packed, SPLIT, Sha, None).is_err());
            assert!(verify_unbatched(statement.semantic_public(), &packed, Sha, None).is_err());
            // Everything before the multiproofs is the pinned proof apart from the magic.
            assert_eq!(&packed[8..compact::OFF_NODES], &proof[8..compact::OFF_NODES]);
            // Node counts: the pinned count function on the merged sets, within the slots.
            let (p, _) = prepared(proof, public);
            for (tree, folded) in [(0usize, false), (1, false), (2, true)] {
                let merged = distinct_sorted(&p.queries, folded);
                let count = multiproof::node_count_merged(&merged).unwrap();
                assert_eq!(count, supplied_positions(&merged).len());
                assert!(count <= format::SLOT_NODES[tree]);
                let slot = &packed[format::slot_offset(tree)..format::slot_offset(tree + 1)];
                assert!(slot[32 * count..].iter().all(|&b| b == 0), "{name} tree {tree} padding");
            }
        }
    }

    #[test]
    fn packed_format_rejects_a_change_in_every_region() {
        let (packed, public) = packed_fixture(2);
        let statement = decode(public);
        let (p, _) = prepared(FIXTURES[2].1, public);
        let mut offsets = mutation_offsets().into_iter().filter(|&at| at < compact::OFF_NODES).collect::<Vec<_>>();
        offsets.extend([0usize, 7, 8, 9, 15]);
        for (tree, folded) in [(0usize, false), (1, false), (2, true)] {
            let count = multiproof::node_count_merged(&distinct_sorted(&p.queries, folded)).unwrap();
            let start = format::slot_offset(tree);
            offsets.extend([start, start + 32 * (count / 2) + 3, start + 32 * count - 1]);
            // Padding: first, middle and last padding byte of the slot.
            let end = format::slot_offset(tree + 1);
            assert!(start + 32 * count < end, "fixture leaves padding in tree {tree}");
            offsets.extend([start + 32 * count, (start + 32 * count + end) / 2, end - 1]);
        }
        for at in (format::OFF_CERTIFICATE..format::PROOF_BYTES).step_by(13) {
            offsets.push(at);
        }
        offsets.push(format::PROOF_BYTES - 1);
        for at in offsets {
            let mut bad = packed.clone();
            bad[at] ^= 1;
            assert!(verify(statement.semantic_public(), &bad, Sha, None).is_err(), "accepted a change at {at}");
        }
        assert!(verify(statement.semantic_public(), &packed[..packed.len() - 1], Sha, None).is_err());
        let mut longer = packed.clone();
        longer.push(0);
        assert!(verify(statement.semantic_public(), &longer, Sha, None).is_err());
    }

    #[test]
    fn merged_slot_bounds_are_attained_by_the_bit_reversed_index_sets() {
        // 22 leaves spread as widely as possible in the 2^18-leaf tree.
        let mut wide: Vec<u32> = (0..22u32).map(|j| j.reverse_bits() >> (32 - multiproof::LEAF_BITS)).collect();
        wide.sort_unstable();
        assert_eq!(multiproof::node_count_merged(&wide), Some(format::SLOT_NODES[0]));
        // 22 folded leaves spread as widely as possible below 2^16.
        let mut folded: Vec<u32> = (0..22u32).map(|j| j.reverse_bits() >> 16).collect();
        folded.sort_unstable();
        assert_eq!(multiproof::node_count_merged(&folded), Some(format::SLOT_NODES[2]));
        // Random sets never exceed the bounds; the count agrees with the 16-capacity function on small sets.
        let mut state = 0x9e3779b97f4a7c15u64;
        for case in 0..2_000 {
            let n = 1 + case % 22;
            let mut set: Vec<u32> = (0..n).map(|_| (next(&mut state) % (1 << 18)) as u32).collect();
            set.sort_unstable();
            set.dedup();
            let count = multiproof::node_count_merged(&set).unwrap();
            assert!(count <= format::SLOT_NODES[0]);
            if set.len() <= multiproof::MAX_BATCH {
                assert_eq!(Some(count), multiproof::node_count(Arity::Two, &set));
            }
            let mut low: Vec<u32> = set.iter().map(|u| u / 4).collect();
            low.dedup();
            assert!(multiproof::node_count_merged(&low).unwrap() <= format::SLOT_NODES[2]);
        }
    }
}
