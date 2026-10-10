//! Unproved COST PROBE; S4 copy.
//! SBF-shaped representation of the existing verifier equations. The owned
//! dense implementation remains the off-chain reference and prover path.
use super::mark;
use super::{
    basis, chord,
    domain::{self, FibreIndex, SlotIndex},
    fold, heap,
    opening::{self, OpeningData, COPY_ACTIVE_ROW_MASKS},
    structured,
    transcript::{OpeningTranscript, SemanticBoundary},
    transport::COEFFICIENT_TO_ROW,
    verifier::Challenges,
    wire::{FibreView, OpeningView},
    Error,
};
use crate::{
    field::{WideExact as E, M31, QM31},
    HashFn,
};
use alloc::{boxed::Box, vec::Vec};
pub struct Prepared {
    pub data: Box<OpeningData>,
    pub challenges: Challenges,
    pub polynomial: [E; 7],
    pub v1: Box<V1Invariants>,
}
/// Fibre-independent values, owned by prepare and borrowed by every V1.
pub struct V1Invariants {
    pub gamma_powers: [E; 29],
    pub interpolant: [E; 3],
    pub line: chord::Secant<QM31>,
    pub alpha_powers: [E; 4],
}
/// The transcript supplies K embeddings. Never silently discard a high limb.
#[inline(never)]
fn subfield_line(data: &OpeningData) -> Result<chord::Secant<QM31>, Error> {
    let line = data.line();
    if [line.a, line.b, line.c]
        .iter()
        .any(|x| x.c1() != QM31::ZERO)
    {
        return Err(Error::WrongField);
    }
    Ok(chord::Secant {
        a: line.a.c0(),
        b: line.b.c0(),
        c: line.c.c0(),
    })
}
#[inline(never)]
fn v1_invariants(data: &OpeningData, gamma: E) -> Result<Box<V1Invariants>, Error> {
    let mut out = heap::uninit::<V1Invariants>()?;
    unsafe {
        let p = out.as_mut_ptr();
        core::ptr::addr_of_mut!((*p).gamma_powers).write(opening::powers::<29>(gamma));
        mark("r0:b:+prepare.interpolant");
        core::ptr::addr_of_mut!((*p).interpolant).write(interpolant(data, &(*p).gamma_powers)?);
        mark("r0:b:-prepare.interpolant");
        core::ptr::addr_of_mut!((*p).line).write(subfield_line(data)?);
        core::ptr::addr_of_mut!((*p).alpha_powers).write([E::ZERO; 4]);
        Ok(out.assume_init())
    }
}
#[inline(never)]
fn data(
    boundary: &SemanticBoundary,
    proof: &OpeningView<'_>,
    z: [domain::Point<E>; 2],
) -> Result<Box<OpeningData>, Error> {
    let mut out = heap::uninit::<OpeningData>()?;
    // Initialize each member at its final heap address. Each y element is
    // canonical because the complete opening was parsed before this call.
    unsafe {
        let p = out.as_mut_ptr();
        core::ptr::addr_of_mut!((*p).roots).write(boundary.roots());
        core::ptr::addr_of_mut!((*p).z).write(z);
        let y = core::ptr::addr_of_mut!((*p).y).cast::<E>();
        for l in 0..29 {
            for j in 0..2 {
                y.add(2 * l + j).write(proof.endpoint(l, j));
            }
        }
        core::ptr::addr_of_mut!((*p).points).write(boundary.points());
        core::ptr::addr_of_mut!((*p).claims).copy_from_nonoverlapping(&boundary.claims, 1);
        Ok(out.assume_init())
    }
}
#[inline(never)]
pub fn prepare(
    hash: HashFn,
    boundary: &SemanticBoundary,
    proof: &OpeningView<'_>,
) -> Result<Prepared, Error> {
    // Retain the prepare-time fibre-count check after canonical parsing.
    if proof.opening_count() != 22 {
        return Err(Error::Parse);
    }
    mark("r0:b:+prepare.transcript_z0");
    let mut t = OpeningTranscript::new(hash, boundary);
    let z0 = t.z0(&boundary.claims)?;
    mark("r0:b:-prepare.transcript_z0");
    mark("r0:b:+prepare.y0_decode");
    let y0 = core::array::from_fn(|j| E::from_le_bytes(&proof.y0[32 * j..32 * j + 32]).unwrap());
    mark("r0:b:-prepare.y0_decode");
    mark("r0:b:+prepare.transcript_z1");
    let z1 = t.z1(&y0)?;
    mark("r0:b:-prepare.transcript_z1");
    mark("r0:b:+prepare.data_copy");
    let data = data(boundary, proof, [z0, z1])?;
    mark("r0:b:-prepare.data_copy");
    mark("r0:b:+prepare.validate_points");
    data.validate_points()?;
    mark("r0:b:-prepare.validate_points");
    mark("r0:b:+prepare.transcript_batch");
    let gamma = t.gamma(&data.y)?;
    let kappa = t.kappa(proof.v)?;
    let tau = t.tau()?;
    mark("r0:b:-prepare.transcript_batch");
    mark("r0:b:+prepare.v1_invariants");
    let mut v1 = v1_invariants(&data, gamma)?;
    mark("r0:b:-prepare.v1_invariants");
    let [c0, c1, c2, c3, c5, c6] = proof.coefficients;
    let c4 = fold::quarter::<E>()
        .mul(claim_prime(&data, gamma, proof.v, kappa, &v1.interpolant)?)
        .sub(c0);
    let polynomial = [c0, c1, c2, c3, c4, c5, c6];
    mark("r0:b:+prepare.transcript_alpha");
    let alpha = t.alpha(&polynomial)?;
    mark("r0:b:-prepare.transcript_alpha");
    mark("r0:b:+prepare.query_sampling");
    let queries = t.queries_canonical_bytes(proof.final_message)?;
    mark("r0:b:-prepare.query_sampling");
    v1.alpha_powers = opening::powers::<4>(alpha);
    #[cfg(all(feature = "r0-e4-reference", not(target_os = "solana")))]
    {
        super::equality_trace::fields(&[z0.x, z0.y, z1.x, z1.y, gamma, kappa, tau, alpha]);
        super::equality_trace::fields(&polynomial);
        super::equality_trace::fields(&v1.gamma_powers);
        super::equality_trace::fields(&v1.interpolant);
        super::equality_trace::fields(&v1.alpha_powers);
    }
    Ok(Prepared {
        data,
        challenges: Challenges {
            gamma,
            kappa,
            tau,
            alpha,
            queries,
        },
        polynomial,
        v1,
    })
}
/// Only coefficients 0,1,2 can be nonzero in liftLinear(interpolationPair).
#[inline(never)]
fn interpolant(data: &OpeningData, g: &[E; 29]) -> Result<[E; 3], Error> {
    let y = core::array::from_fn(|j| (0..29).fold(E::ZERO, |s, l| s.add(g[l].mul(data.y[l][j]))));
    mark("r0:b:+prepare.chord_pair");
    let p = chord::interpolation_pair(data.z[0], data.z[1], y)?;
    mark("r0:b:-prepare.chord_pair");
    Ok([p.p0[0], p.p1, p.p0[1]])
}
const fn indicator_bits() -> [u16; 64] {
    let mut bits = [0; 64];
    let mut j = 0;
    while j < 1024 {
        let r = COEFFICIENT_TO_ROW[j] as usize;
        if (COPY_ACTIVE_ROW_MASKS[r / 16] >> (r % 16)) & 1 == 0 {
            bits[j / 16] |= 1 << (j % 16);
        }
        j += 1;
    }
    bits
}
pub const INDICATOR_BITS: [u16; 64] = indicator_bits();
fn indicator(j: usize) -> E {
    if (INDICATOR_BITS[j / 16] >> (j % 16)) & 1 == 1 {
        E::ONE
    } else {
        E::ZERO
    }
}
fn eq_at(p: &[E; 10], row: usize) -> QM31 {
    // These coordinates are K embeddings from the checked semantic alphas;
    // no proof-supplied E coordinate is narrowed by this specialization.
    (0..10).fold(QM31::ONE, |v, b| {
        v.mul(if (row >> b) & 1 == 0 {
            QM31::ONE.sub(p[b].c0())
        } else {
            p[b].c0()
        })
    })
}
fn weight_at(data: &OpeningData, k: &[E; 4], j: usize) -> E {
    (0..3).fold(indicator(j), |v, p| {
        v.add(k[p + 1].mul_qm31(eq_at(&data.points[p], COEFFICIENT_TO_ROW[j] as usize)))
    })
}
#[inline(never)]
fn claim_prime(data: &OpeningData, gamma: E, v: E, kappa: E, i: &[E; 3]) -> Result<E, Error> {
    mark("r0:b:+prepare.claim_prime");
    let claim = data.claim(gamma, v, kappa);
    let k = opening::powers::<4>(kappa);
    // Exactly the dense dot product with its 1021 zero terms omitted.
    let dot = (0..3).fold(E::ZERO, |v, j| v.add(weight_at(data, &k, j).mul(i[j])));
    mark("r0:b:-prepare.claim_prime");
    Ok(claim.sub(dot))
}
#[inline(never)]
pub fn check_v1(
    invariants: &V1Invariants,
    proof: &OpeningView<'_>,
    u: FibreIndex,
    opening: &FibreView<'_>,
    diagnostic: bool,
) -> Result<(), Error> {
    let g = &invariants.gamma_powers;
    let i = &invariants.interpolant;
    let line = &invariants.line;
    let mut r = [E::ZERO; 4];
    for s in 0..4 {
        let index = domain::child_index(u, SlotIndex::new(s)?);
        let point = domain::stored_point::<M31>(index);
        if diagnostic {
            mark("r0:b:+v1.dots");
        }
        let dot = (0..29).fold(E::ZERO, |v, l| {
            if diagnostic {
                mark("r0:b:+v1.value_decode");
            }
            let x = opening.value(s, l);
            if diagnostic {
                mark("r0:b:-v1.value_decode");
            }
            v.add(if l < 26 {
                g[l].mul_m31(M31(x.to_limbs()[0]))
            } else {
                g[l].mul_qm31(x.c0())
            })
        });
        if diagnostic {
            mark("r0:b:-v1.dots");
            mark("r0:b:+v1.numerator");
        }
        let numerator = dot.sub(i[0].add(i[2].mul_m31(point.x)).add(i[1].mul_m31(point.y)));
        if diagnostic {
            mark("r0:b:-v1.numerator");
            mark("r0:b:+v1.inversions_products");
        }
        r[s] = numerator.mul_qm31(
            line.a
                .add(line.b.mul_m31(point.x))
                .add(line.c.mul_m31(point.y))
                .try_inv()
                .ok_or(Error::ZeroDenominator)?,
        );
        if diagnostic {
            mark("r0:b:-v1.inversions_products");
        }
    }
    #[cfg(all(feature = "r0-e4-reference", not(target_os = "solana")))]
    super::equality_trace::fields(&r);
    if diagnostic {
        mark("r0:b:+v1.fold");
    }
    let point = domain::fibre_point(u);
    let h = fold::phi(point.x, point.y, r)?;
    let a = &invariants.alpha_powers;
    // The same degree-three fold polynomial, using the prepared powers.
    let lhs = h[0]
        .add(a[1].mul(h[1]))
        .add(a[2].mul(h[2]))
        .add(a[3].mul(h[3]));
    if diagnostic {
        mark("r0:b:-v1.fold");
        mark("r0:b:+v1.final_encoder");
    }
    let rhs = final_encoder(proof, u);
    if diagnostic {
        mark("r0:b:-v1.final_encoder");
    }
    #[cfg(all(feature = "r0-hoist-reference", not(target_os = "solana")))]
    assert_eq!(
        lhs.to_le_bytes(),
        fold::fold_fibre(a[1], u, r)?.to_le_bytes()
    );
    #[cfg(all(feature = "r0-e4-reference", not(target_os = "solana")))]
    super::equality_trace::fields(&[lhs, rhs]);
    if lhs != rhs {
        return Err(Error::V1);
    }
    Ok(())
}
#[inline(never)]
fn final_encoder(proof: &OpeningView<'_>, u: FibreIndex) -> E {
    let values = basis::values::<M31, 256>(domain::line_node(u));
    values.iter().enumerate().fold(E::ZERO, |v, (j, &x)| {
        v.add(proof.final_coefficient(j).mul_m31(x))
    })
}
/// Tensor values remain in row order; the pairing applies the D13 permutation.
fn eq_tensor(p: &[E; 10], eq: &mut [QM31]) {
    eq[0] = QM31::ONE;
    let mut width = 1;
    for b in 0..10 {
        let x = p[b].c0();
        for j in 0..width {
            let v = eq[j];
            let right = v.mul(x);
            eq[j + width] = right;
            eq[j] = v.sub(right);
        }
        width *= 2;
    }
}
#[inline(never)]
pub fn check_v2(
    data: &OpeningData,
    kappa: E,
    tau: E,
    alpha: E,
    c: &[E; 7],
    proof: &OpeningView<'_>,
) -> Result<(), Error> {
    mark("r0:b:+v2.G");
    let lhs = c.iter().rev().fold(E::ZERO, |v, &c| v.mul(alpha).add(c));
    // G = dF^T F in channel order [0,3,2,1]. The three nontrivial
    // powers are applied successively to each F entry, with no inversions.
    let mut g = heap::filled(1024, E::ZERO)?;
    for j in 0..256 {
        let f = proof.final_coefficient(j);
        let af = f.mul(alpha);
        let a2f = af.mul(alpha);
        let a3f = a2f.mul(alpha);
        g[4 * j] = f;
        g[4 * j + 1] = a3f;
        g[4 * j + 2] = a2f;
        g[4 * j + 3] = af;
    }
    let mut even = heap::filled(512, E::ZERO)?;
    mark("r0:b:-v2.G");
    mark("r0:b:+v2.workspace_line");
    let mut odd = heap::filled(512, E::ZERO)?;
    let mut twice = heap::filled(512, E::ZERO)?;
    let line = subfield_line(data)?;
    mark("r0:b:-v2.workspace_line");
    mark("r0:b:+v2.images");
    let tau2 = tau.mul(tau);
    let top = structured::top_rows(511)[1];
    let image1 = g[1023].mul_m31(top).mul(tau);
    let image2 = g[1022]
        .mul_qm31(line.b.mul_m31(top))
        .add(g[1021].mul_qm31(line.c.neg().mul_m31(structured::top_rows(510)[0])))
        .mul(tau2);
    mark("r0:b:-v2.images");
    mark("r0:b:+v2.chord_weights");
    structured::chord_weights(line, &mut g, &mut even, &mut odd, &mut twice)?;
    mark("r0:b:-v2.chord_weights");
    mark("r0:b:+v2.indicator_sum");
    let mut dot = E::ZERO;
    for j in 0..1024 {
        if (INDICATOR_BITS[j / 16] >> (j % 16)) & 1 == 1 {
            dot = dot.add(g[j]);
        }
    }
    mark("r0:b:-v2.indicator_sum");
    let k = opening::powers::<4>(kappa);
    let mut eq = heap::filled(1024, QM31::ZERO)?;
    for p in 0..3 {
        mark("r0:b:+v2.tensor");
        eq_tensor(&data.points[p], &mut eq);
        mark("r0:b:-v2.tensor");
        mark("r0:b:+v2.pairing");
        let mut pairing = E::ZERO;
        for j in 0..1024 {
            pairing = pairing.add(g[j].mul_qm31(eq[COEFFICIENT_TO_ROW[j] as usize]));
        }
        dot = dot.add(k[p + 1].mul(pairing));
        mark("r0:b:-v2.pairing");
    }
    mark("r0:b:+v2.image_combine");
    dot = dot.add(image1).add(image2);
    let rhs = fold::quarter::<E>().mul(dot);
    mark("r0:b:-v2.image_combine");
    #[cfg(all(feature = "r0-e4-reference", not(target_os = "solana")))]
    super::equality_trace::fields(&[lhs, rhs]);
    if lhs != rhs {
        return Err(Error::V2);
    }
    Ok(())
}
