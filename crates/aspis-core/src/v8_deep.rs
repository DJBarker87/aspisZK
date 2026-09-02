//! Isolated no-new-tree two-point DEEP research path for V8-A100.
//!
//! The functions in this module consume only the 29 component values already
//! authenticated by the C1/C2 leaves. They do not parse or authenticate a
//! quotient leaf, root, or frontier. The reference path favors literal
//! formulas; the optimized path uses one-pass query decoding, a shared gamma
//! power table, a three-output dot for the first opening plus both public OOD
//! vectors, and one batch inversion for all q22 four-slot denominators.

use crate::circle::{secure_ood_circle_point_from_parameter, SecureCirclePoint};
use crate::circle_fri::{selected_circle_fiber_points_shared, BaseCirclePoint};
use crate::field::{qm31_dot, qm31_dot3, qm31_power_table, CM31, M31, QM31};
use crate::transcript::{label, Transcript};
use crate::v6_onefold::{
    decode_packed_m31_eight_aligned, packed_m31_at, packed_qm31_at, V6WireError, V6_C1_COLUMNS,
    V6_C1_LIMBS_PER_QUERY, V6_C2_COLUMNS, V6_C2_LIMBS_PER_QUERY,
};
use crate::v8_a100::{
    V8A100QueryRecord, V8A100Wire, V8_A100_COMPONENTS, V8_A100_OOD_POINTS, V8_A100_QUERY_COUNT,
};

pub const V8_A100_CIRCLE_DOMAIN_LOG_SIZE: u32 = 20;
pub const V8_A100_FIBRE_SLOTS: usize = 4;
pub const V8_A100_DEEP_DENOMINATORS: usize = V8_A100_QUERY_COUNT * V8_A100_FIBRE_SLOTS;
pub const V8_A100_DISTINCT_POINT_RETRY_LIMIT: usize = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V8DeepError {
    Wire(V6WireError),
    ChallengeSampling,
    InvalidOodPoint,
    DuplicateOodPoint,
    ComponentVectorMismatch,
    ZeroDenominator,
    CircleGeometry,
}

impl From<V6WireError> for V8DeepError {
    fn from(value: V6WireError) -> Self {
        Self::Wire(value)
    }
}

#[derive(Clone)]
pub struct V8A100OodPrefix {
    pub points: [SecureCirclePoint; V8_A100_OOD_POINTS],
    pub parameters: [QM31; V8_A100_OOD_POINTS],
    /// State after both vectors, but deliberately before batch work and
    /// gamma. The production caller must check and absorb batch work first.
    pub continuation: Transcript,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V8A100TwoPointChallenges {
    pub points: [SecureCirclePoint; V8_A100_OOD_POINTS],
    pub component_evaluations: [[QM31; V8_A100_COMPONENTS]; V8_A100_OOD_POINTS],
    pub gamma: QM31,
}

fn absorb_component_vector(
    transcript: &mut Transcript,
    sample: usize,
    values: &[QM31; V8_A100_COMPONENTS],
) {
    let mut record = [0u8; 1 + 16 * V8_A100_COMPONENTS];
    record[0] = sample as u8;
    for (component, value) in values.iter().copied().enumerate() {
        value.write_le_bytes(&mut record[1 + 16 * component..1 + 16 * (component + 1)]);
    }
    transcript.absorb(label::V8_COMPONENT_OOD_VECTOR, &record);
}

/// Execute the adaptive-safe OOD prefix:
/// `zeta0; vector0; zeta1 (distinct); vector1`.
///
/// The returned transcript has not sampled gamma. This makes it impossible
/// for this helper to accidentally move gamma ahead of the existing batch
/// work stage.
pub fn derive_v8_a100_ood_prefix(
    transcript: &Transcript,
    component_evaluations: &[[QM31; V8_A100_COMPONENTS]; V8_A100_OOD_POINTS],
) -> Result<V8A100OodPrefix, V8DeepError> {
    let mut continuation = transcript.clone();
    let point0 = continuation
        .challenge_secure_circle_point()
        .map_err(|_| V8DeepError::ChallengeSampling)?;
    let parameter0 = recover_secure_circle_parameter(point0)?;
    absorb_component_vector(&mut continuation, 0, &component_evaluations[0]);

    let mut selected1 = None;
    for _ in 0..V8_A100_DISTINCT_POINT_RETRY_LIMIT {
        let candidate = continuation
            .challenge_secure_circle_point()
            .map_err(|_| V8DeepError::ChallengeSampling)?;
        if candidate != point0 {
            selected1 = Some(candidate);
            break;
        }
    }
    let point1 = selected1.ok_or(V8DeepError::DuplicateOodPoint)?;
    let parameter1 = recover_secure_circle_parameter(point1)?;
    absorb_component_vector(&mut continuation, 1, &component_evaluations[1]);

    Ok(V8A100OodPrefix {
        points: [point0, point1],
        parameters: [parameter0, parameter1],
        continuation,
    })
}

/// Sample gamma only after the caller has checked and absorbed V8 batch work.
pub fn sample_v8_a100_gamma(
    transcript_after_batch_work: &mut Transcript,
) -> Result<QM31, V8DeepError> {
    transcript_after_batch_work
        .challenge_nonzero_qm31()
        .map_err(|_| V8DeepError::ChallengeSampling)
}

/// Invert the finite rational circle map with `t = y / (1+x)` and recheck
/// the secure OOD policy. This rejects malformed, in-domain, and `x = -1`
/// proof/API inputs without a panicking inverse.
pub fn recover_secure_circle_parameter(point: SecureCirclePoint) -> Result<QM31, V8DeepError> {
    if point.x.square().add(point.y.square()) != QM31::ONE {
        return Err(V8DeepError::InvalidOodPoint);
    }
    let inverse = QM31::ONE
        .add(point.x)
        .try_inv()
        .ok_or(V8DeepError::InvalidOodPoint)?;
    let parameter = point.y.mul(inverse);
    let recovered = secure_ood_circle_point_from_parameter(parameter)
        .map_err(|_| V8DeepError::InvalidOodPoint)?;
    if recovered != point {
        return Err(V8DeepError::InvalidOodPoint);
    }
    Ok(parameter)
}

#[inline(always)]
fn embed_m31(value: u32) -> QM31 {
    QM31::from_cm31(CM31::from_m31(M31(value)))
}

/// Literal random-access decoder used as the independent slow reference.
pub fn decode_v8_query_components_reference(
    query: V8A100QueryRecord<'_>,
) -> Result<[[QM31; V8_A100_COMPONENTS]; V8_A100_FIBRE_SLOTS], V8DeepError> {
    let mut components = [[QM31::ZERO; V8_A100_COMPONENTS]; V8_A100_FIBRE_SLOTS];
    for (slot, row) in components.iter_mut().enumerate() {
        for (column, value) in row[..V6_C1_COLUMNS].iter_mut().enumerate() {
            *value = embed_m31(
                packed_m31_at(query.c1_packed, slot * V6_C1_COLUMNS + column)
                    .ok_or(V8DeepError::Wire(V6WireError::WrongLength))?,
            );
        }
        for helper in 0..V6_C2_COLUMNS {
            row[V6_C1_COLUMNS + helper] =
                packed_qm31_at(query.c2_packed, helper * V8_A100_FIBRE_SLOTS + slot)
                    .ok_or(V8DeepError::Wire(V6WireError::WrongLength))?;
        }
    }
    Ok(components)
}

/// One-pass aligned decoder for the intended verifier path.
pub fn decode_v8_query_components_optimized(
    query: V8A100QueryRecord<'_>,
) -> Result<[[QM31; V8_A100_COMPONENTS]; V8_A100_FIBRE_SLOTS], V8DeepError> {
    let c1 = decode_packed_m31_eight_aligned::<V6_C1_LIMBS_PER_QUERY>(query.c1_packed)?;
    let c2 = decode_packed_m31_eight_aligned::<V6_C2_LIMBS_PER_QUERY>(query.c2_packed)?;
    let mut components = [[QM31::ZERO; V8_A100_COMPONENTS]; V8_A100_FIBRE_SLOTS];
    for (slot, row) in components.iter_mut().enumerate() {
        for (column, value) in row[..V6_C1_COLUMNS].iter_mut().enumerate() {
            *value = embed_m31(c1[slot * V6_C1_COLUMNS + column]);
        }
        for helper in 0..V6_C2_COLUMNS {
            let limb = 4 * (helper * V8_A100_FIBRE_SLOTS + slot);
            row[V6_C1_COLUMNS + helper] = QM31 {
                c0: CM31::new(M31(c2[limb]), M31(c2[limb + 1])),
                c1: CM31::new(M31(c2[limb + 2]), M31(c2[limb + 3])),
            };
        }
    }
    Ok(components)
}

fn gamma_dot_reference(gamma: QM31, values: &[QM31; V8_A100_COMPONENTS]) -> QM31 {
    let mut power = QM31::ONE;
    let mut sum = QM31::ZERO;
    for value in values {
        sum = sum.add(power.mul(*value));
        power = power.mul(gamma);
    }
    sum
}

#[inline(always)]
fn two_point_interpolant(
    point: SecureCirclePoint,
    points: [SecureCirclePoint; 2],
    values: [QM31; 2],
    inverse_difference: QM31,
    use_x: bool,
) -> QM31 {
    // I(P) is the affine circle function obtained from a separating
    // coordinate h: A*(h-h1)/(h0-h1) + B*(h-h0)/(h1-h0).
    let coordinate = if use_x { point.x } else { point.y };
    let coordinates = if use_x {
        [points[0].x, points[1].x]
    } else {
        [points[0].y, points[1].y]
    };
    values[0]
        .mul(coordinate.sub(coordinates[1]))
        .sub(values[1].mul(coordinate.sub(coordinates[0])))
        .mul(inverse_difference)
}

#[inline(always)]
fn two_point_chord_zerofier(point: SecureCirclePoint, points: [SecureCirclePoint; 2]) -> QM31 {
    // The affine chord through z0,z1:
    // det [[1,x,y],[1,x0,y0],[1,x1,y1]].  Restricted to the circle it has
    // exactly those two roots.  This, rather than (t-t0)(t-t1), is the
    // degree-one circle factor compatible with the existing fold basis.
    let constant = points[0]
        .x
        .mul(points[1].y)
        .sub(points[0].y.mul(points[1].x));
    let x_coefficient = points[0].y.sub(points[1].y);
    let y_coefficient = points[1].x.sub(points[0].x);
    constant
        .add(x_coefficient.mul(point.x))
        .add(y_coefficient.mul(point.y))
}

fn validate_challenges(challenges: &V8A100TwoPointChallenges) -> Result<(bool, QM31), V8DeepError> {
    if challenges.points[0] == challenges.points[1] {
        return Err(V8DeepError::DuplicateOodPoint);
    }
    let parameters = [
        recover_secure_circle_parameter(challenges.points[0])?,
        recover_secure_circle_parameter(challenges.points[1])?,
    ];
    if parameters[0] == parameters[1] {
        return Err(V8DeepError::DuplicateOodPoint);
    }
    let use_x = challenges.points[0].x != challenges.points[1].x;
    let difference = if use_x {
        challenges.points[0].x.sub(challenges.points[1].x)
    } else {
        challenges.points[0].y.sub(challenges.points[1].y)
    };
    let inverse_difference = difference.try_inv().ok_or(V8DeepError::DuplicateOodPoint)?;
    Ok((use_x, inverse_difference))
}

/// Literal per-opening circle quotient with independent gamma loops and
/// inversion.  The denominator is the affine chord through the two OOD
/// points, not the product of their stereographic-parameter differences.
pub fn v8_two_point_circle_quotient_reference(
    component_values: &[QM31; V8_A100_COMPONENTS],
    query_point: SecureCirclePoint,
    challenges: &V8A100TwoPointChallenges,
) -> Result<QM31, V8DeepError> {
    let (use_x, inverse_difference) = validate_challenges(challenges)?;
    let combined = gamma_dot_reference(challenges.gamma, component_values);
    let evaluations = [
        gamma_dot_reference(challenges.gamma, &challenges.component_evaluations[0]),
        gamma_dot_reference(challenges.gamma, &challenges.component_evaluations[1]),
    ];
    let numerator = combined.sub(two_point_interpolant(
        query_point,
        challenges.points,
        evaluations,
        inverse_difference,
        use_x,
    ));
    let inverse_zerofier = two_point_chord_zerofier(query_point, challenges.points)
        .try_inv()
        .ok_or(V8DeepError::ZeroDenominator)?;
    Ok(numerator.mul(inverse_zerofier))
}

#[derive(Clone)]
struct PreparedDeep {
    powers: [QM31; V8_A100_COMPONENTS],
    points: [SecureCirclePoint; 2],
    use_x: bool,
    inverse_difference: QM31,
    evaluations: [QM31; 2],
}

fn prepare_deep(challenges: &V8A100TwoPointChallenges) -> Result<PreparedDeep, V8DeepError> {
    let (use_x, inverse_difference) = validate_challenges(challenges)?;
    let powers = qm31_power_table(challenges.gamma);
    let evaluations = [
        qm31_dot(&powers, &challenges.component_evaluations[0]),
        qm31_dot(&powers, &challenges.component_evaluations[1]),
    ];
    Ok(PreparedDeep {
        powers,
        points: challenges.points,
        use_x,
        inverse_difference,
        evaluations,
    })
}

fn batch_inverse<const N: usize>(values: &[QM31; N]) -> Result<[QM31; N], V8DeepError> {
    let mut prefixes = [QM31::ONE; N];
    let mut product = QM31::ONE;
    for (index, value) in values.iter().copied().enumerate() {
        if value == QM31::ZERO {
            return Err(V8DeepError::ZeroDenominator);
        }
        prefixes[index] = product;
        product = product.mul(value);
    }
    let mut inverse = product.try_inv().ok_or(V8DeepError::ZeroDenominator)?;
    let mut output = [QM31::ZERO; N];
    for index in (0..N).rev() {
        output[index] = inverse.mul(prefixes[index]);
        inverse = inverse.mul(values[index]);
    }
    Ok(output)
}

fn embed_base_circle_point(point: BaseCirclePoint) -> SecureCirclePoint {
    SecureCirclePoint {
        x: embed_m31(point.x.0),
        y: embed_m31(point.y.0),
    }
}

fn query_circle_points(
    queries: [u32; V8_A100_QUERY_COUNT],
) -> Result<[[SecureCirclePoint; V8_A100_FIBRE_SLOTS]; V8_A100_QUERY_COUNT], V8DeepError> {
    let slot_zero = selected_circle_fiber_points_shared(V8_A100_CIRCLE_DOMAIN_LOG_SIZE, &queries)
        .map_err(|_| V8DeepError::CircleGeometry)?;
    if slot_zero.len() != V8_A100_QUERY_COUNT {
        return Err(V8DeepError::CircleGeometry);
    }
    let zero = SecureCirclePoint {
        x: QM31::ZERO,
        y: QM31::ZERO,
    };
    let mut points = [[zero; V8_A100_FIBRE_SLOTS]; V8_A100_QUERY_COUNT];
    for (query, point) in slot_zero.into_iter().enumerate() {
        let slots = [
            point,
            BaseCirclePoint {
                x: point.x,
                y: point.y.neg(),
            },
            BaseCirclePoint {
                x: point.x.neg(),
                y: point.y.neg(),
            },
            BaseCirclePoint {
                x: point.x.neg(),
                y: point.y,
            },
        ];
        for (slot, point) in slots.into_iter().enumerate() {
            points[query][slot] = embed_base_circle_point(point);
        }
    }
    Ok(points)
}

/// Slow end-to-end wire reference: random-access component decoding, repeated
/// gamma loops, and one field inversion per quotient.
pub fn v8_deep_quotients_reference_wire(
    wire: &V8A100Wire<'_>,
    queries: [u32; V8_A100_QUERY_COUNT],
    challenges: &V8A100TwoPointChallenges,
) -> Result<[[QM31; V8_A100_FIBRE_SLOTS]; V8_A100_QUERY_COUNT], V8DeepError> {
    if wire.component_ood_vectors() != Some(challenges.component_evaluations) {
        return Err(V8DeepError::ComponentVectorMismatch);
    }
    let points = query_circle_points(queries)?;
    let mut output = [[QM31::ZERO; V8_A100_FIBRE_SLOTS]; V8_A100_QUERY_COUNT];
    for query in 0..V8_A100_QUERY_COUNT {
        let record = wire
            .query(query)
            .ok_or(V8DeepError::Wire(V6WireError::WrongLength))?;
        let components = decode_v8_query_components_reference(record)?;
        for slot in 0..V8_A100_FIBRE_SLOTS {
            output[query][slot] = v8_two_point_circle_quotient_reference(
                &components[slot],
                points[query][slot],
                challenges,
            )?;
        }
    }
    Ok(output)
}

/// Intended no-new-tree verifier path. All inputs come from the two existing
/// authenticated query records and the fixed component vectors. Exactly one
/// QM31 inversion handles all 88 query zerofiers.
pub fn v8_deep_quotients_optimized_wire(
    wire: &V8A100Wire<'_>,
    queries: [u32; V8_A100_QUERY_COUNT],
    challenges: &V8A100TwoPointChallenges,
) -> Result<[[QM31; V8_A100_FIBRE_SLOTS]; V8_A100_QUERY_COUNT], V8DeepError> {
    if wire.component_ood_vectors() != Some(challenges.component_evaluations) {
        return Err(V8DeepError::ComponentVectorMismatch);
    }
    let mut prepared = prepare_deep(challenges)?;
    let points = query_circle_points(queries)?;
    let mut numerators = [[QM31::ZERO; V8_A100_FIBRE_SLOTS]; V8_A100_QUERY_COUNT];
    let mut denominators = [QM31::ZERO; V8_A100_DEEP_DENOMINATORS];

    for query in 0..V8_A100_QUERY_COUNT {
        let record = wire
            .query(query)
            .ok_or(V8DeepError::Wire(V6WireError::WrongLength))?;
        let components = decode_v8_query_components_optimized(record)?;
        for slot in 0..V8_A100_FIBRE_SLOTS {
            let combined = if query == 0 && slot == 0 {
                // Share each gamma-power decomposition across an authenticated
                // opening and both public component vectors.
                let shared = qm31_dot3(
                    &prepared.powers,
                    [
                        &components[slot],
                        &challenges.component_evaluations[0],
                        &challenges.component_evaluations[1],
                    ],
                );
                prepared.evaluations = [shared[1], shared[2]];
                shared[0]
            } else {
                qm31_dot(&prepared.powers, &components[slot])
            };
            let point = points[query][slot];
            numerators[query][slot] = combined.sub(two_point_interpolant(
                point,
                prepared.points,
                prepared.evaluations,
                prepared.inverse_difference,
                prepared.use_x,
            ));
            denominators[query * V8_A100_FIBRE_SLOTS + slot] =
                two_point_chord_zerofier(point, prepared.points);
        }
    }

    let inverses = batch_inverse(&denominators)?;
    let mut output = [[QM31::ZERO; V8_A100_FIBRE_SLOTS]; V8_A100_QUERY_COUNT];
    for query in 0..V8_A100_QUERY_COUNT {
        for slot in 0..V8_A100_FIBRE_SLOTS {
            output[query][slot] =
                numerators[query][slot].mul(inverses[query * V8_A100_FIBRE_SLOTS + slot]);
        }
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::P;
    use crate::transcript::label;
    use crate::v8_a100::{
        V8A100Wire, V8_A100_MAX_BODY_BYTES, V8_A100_MAX_FRONTIER_FIXTURE, V8_A100_MAX_QUERY_DRAWS,
        V8_A100_PROFILE_BINDING,
    };
    use alloc::vec;
    use sha2::{Digest, Sha256};

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(
                M31(seed % P),
                M31(seed.wrapping_mul(17).wrapping_add(3) % P),
            ),
            c1: CM31::new(
                M31(seed.wrapping_mul(31).wrapping_add(5) % P),
                M31(seed.wrapping_mul(47).wrapping_add(7) % P),
            ),
        }
    }

    fn challenges() -> V8A100TwoPointChallenges {
        let parameters = [q(101), q(202)];
        V8A100TwoPointChallenges {
            points: [
                secure_ood_circle_point_from_parameter(parameters[0]).unwrap(),
                secure_ood_circle_point_from_parameter(parameters[1]).unwrap(),
            ],
            component_evaluations: core::array::from_fn(|sample| {
                core::array::from_fn(|component| q(1_000 + 97 * sample as u32 + component as u32))
            }),
            gamma: q(303),
        }
    }

    fn pack_m31(values: &[u32]) -> alloc::vec::Vec<u8> {
        let mut out = vec![0u8; (31 * values.len() + 7) / 8];
        for (index, value) in values.iter().copied().enumerate() {
            assert!(value < P);
            let bit_start = 31 * index;
            for bit in 0..31 {
                if (value >> bit) & 1 != 0 {
                    out[(bit_start + bit) / 8] |= 1 << ((bit_start + bit) % 8);
                }
            }
        }
        out
    }

    fn query_bytes(seed: u32) -> (alloc::vec::Vec<u8>, alloc::vec::Vec<u8>) {
        let c1: alloc::vec::Vec<u32> = (0..V6_C1_LIMBS_PER_QUERY)
            .map(|index| seed.wrapping_add(13 * index as u32) % P)
            .collect();
        let c2: alloc::vec::Vec<u32> = (0..V6_C2_LIMBS_PER_QUERY)
            .map(|index| seed.wrapping_add(29 * index as u32 + 7) % P)
            .collect();
        (pack_m31(&c1), pack_m31(&c2))
    }

    fn populated_wire() -> (alloc::vec::Vec<u8>, V8A100TwoPointChallenges) {
        let mut body = vec![0u8; V8_A100_MAX_BODY_BYTES];
        let challenges = challenges();
        let fixed = crate::v8_a100::V8_A100_FIXED_PACKED_FIELD_BYTES;
        let mut fixed_limbs = vec![0u32; crate::v8_a100::V8_A100_FIXED_M31_LIMBS];
        for sample in 0..V8_A100_OOD_POINTS {
            for component in 0..V8_A100_COMPONENTS {
                let value = challenges.component_evaluations[sample][component];
                let field_index = crate::v8_a100::V8_A100_COMPONENT_VECTOR_QM31_OFFSET
                    + sample * V8_A100_COMPONENTS
                    + component;
                let limb = 4 * field_index;
                fixed_limbs[limb] = value.c0.a.0;
                fixed_limbs[limb + 1] = value.c0.b.0;
                fixed_limbs[limb + 2] = value.c1.a.0;
                fixed_limbs[limb + 3] = value.c1.b.0;
            }
        }
        body[..fixed].copy_from_slice(&pack_m31(&fixed_limbs));
        let roots_and_work =
            crate::v8_a100::V8_A100_ROOT_BYTES + crate::v6_onefold::V6_WORK_NONCE_BYTES;
        let query_start = fixed + roots_and_work;
        for ordinal in 0..V8_A100_QUERY_COUNT {
            let (c1, c2) = query_bytes(71 + ordinal as u32 * 101);
            let start = query_start + ordinal * crate::v8_a100::V8_A100_QUERY_BYTES;
            body[start..start + c1.len()].copy_from_slice(&c1);
            body[start + c1.len()..start + c1.len() + c2.len()].copy_from_slice(&c2);
        }
        (body, challenges)
    }

    #[test]
    fn transcript_prefix_fixes_vector_zero_before_point_one() {
        let mut transcript = Transcript::new(test_hash);
        transcript.absorb(label::PROFILE, &V8_A100_PROFILE_BINDING);
        transcript.absorb(label::STATEMENT, &[0x5a; 32]);
        let vectors = challenges().component_evaluations;
        let prefix = derive_v8_a100_ood_prefix(&transcript, &vectors).unwrap();
        assert_ne!(prefix.points[0], prefix.points[1]);

        let mut altered = vectors;
        altered[0][7] = altered[0][7].add(QM31::ONE);
        let altered_prefix = derive_v8_a100_ood_prefix(&transcript, &altered).unwrap();
        assert_eq!(prefix.points[0], altered_prefix.points[0]);
        assert_ne!(prefix.points[1], altered_prefix.points[1]);
        assert_ne!(
            prefix.continuation.diagnostic_state(),
            altered_prefix.continuation.diagnostic_state()
        );

        let mut reordered = vectors;
        reordered[0].swap(0, 1);
        let reordered_prefix = derive_v8_a100_ood_prefix(&transcript, &reordered).unwrap();
        assert_ne!(prefix.points[1], reordered_prefix.points[1]);

        let mut before_work = prefix.continuation.clone();
        before_work.absorb(label::GRIND_NONCE, &[0x33; 8]);
        let gamma = sample_v8_a100_gamma(&mut before_work).unwrap();
        assert_ne!(gamma, QM31::ZERO);
    }

    #[test]
    fn malformed_ood_inputs_and_zero_denominators_reject() {
        let valid = challenges();
        let mut duplicate = valid;
        duplicate.points[1] = duplicate.points[0];
        assert_eq!(
            v8_two_point_circle_quotient_reference(
                &[QM31::ZERO; V8_A100_COMPONENTS],
                secure_ood_circle_point_from_parameter(q(999)).unwrap(),
                &duplicate,
            ),
            Err(V8DeepError::DuplicateOodPoint)
        );

        let in_domain = SecureCirclePoint {
            x: QM31::ONE,
            y: QM31::ZERO,
        };
        assert_eq!(
            recover_secure_circle_parameter(in_domain),
            Err(V8DeepError::InvalidOodPoint)
        );
        assert_eq!(
            v8_two_point_circle_quotient_reference(
                &[QM31::ZERO; V8_A100_COMPONENTS],
                valid.points[0],
                &valid,
            ),
            Err(V8DeepError::ZeroDenominator)
        );
    }

    #[test]
    fn reference_and_optimized_decoders_agree() {
        let (c1, c2) = query_bytes(77);
        let salt = [0u8; 32];
        let record = V8A100QueryRecord {
            c1_packed: &c1,
            c2_packed: &c2,
            salt: &salt,
        };
        assert_eq!(
            decode_v8_query_components_reference(record).unwrap(),
            decode_v8_query_components_optimized(record).unwrap()
        );
    }

    #[test]
    fn reference_and_prepared_quotients_agree_over_generated_cases() {
        let challenges = challenges();
        let prepared = prepare_deep(&challenges).unwrap();
        for case in 1..=128u32 {
            let components: [QM31; V8_A100_COMPONENTS] =
                core::array::from_fn(|index| q(case * 10_003 + index as u32 * 211));
            let point = secure_ood_circle_point_from_parameter(q(50_000 + case * 19)).unwrap();
            if two_point_chord_zerofier(point, prepared.points) == QM31::ZERO {
                continue;
            }
            let expected =
                v8_two_point_circle_quotient_reference(&components, point, &challenges).unwrap();
            let combined = qm31_dot(&prepared.powers, &components);
            let numerator = combined.sub(two_point_interpolant(
                point,
                prepared.points,
                prepared.evaluations,
                prepared.inverse_difference,
                prepared.use_x,
            ));
            let actual = numerator.mul(
                two_point_chord_zerofier(point, prepared.points)
                    .try_inv()
                    .unwrap(),
            );
            assert_eq!(actual, expected, "case {case}");
        }
    }

    #[test]
    fn no_new_tree_wire_path_matches_slow_reference() {
        let (body, challenges) = populated_wire();
        let wire = V8A100Wire::parse_for_schedule(
            &body,
            V8_A100_MAX_FRONTIER_FIXTURE,
            crate::v8_a100::V8_A100_FRONTIER_MAX_PER_TREE,
        )
        .unwrap();
        let reference =
            v8_deep_quotients_reference_wire(&wire, V8_A100_MAX_FRONTIER_FIXTURE, &challenges)
                .unwrap();
        let optimized =
            v8_deep_quotients_optimized_wire(&wire, V8_A100_MAX_FRONTIER_FIXTURE, &challenges)
                .unwrap();
        assert_eq!(optimized, reference);
        assert_eq!(
            wire.component_ood_vectors(),
            Some(challenges.component_evaluations)
        );

        let mut altered = challenges;
        altered.gamma = altered.gamma.add(QM31::ONE);
        let changed =
            v8_deep_quotients_optimized_wire(&wire, V8_A100_MAX_FRONTIER_FIXTURE, &altered)
                .unwrap();
        assert_ne!(changed, optimized);

        let mut altered_vector = challenges;
        altered_vector.component_evaluations[0][0] =
            altered_vector.component_evaluations[0][0].add(QM31::ONE);
        assert_eq!(
            v8_deep_quotients_optimized_wire(&wire, V8_A100_MAX_FRONTIER_FIXTURE, &altered_vector),
            Err(V8DeepError::ComponentVectorMismatch)
        );
    }

    #[test]
    fn wire_mutation_changes_quotient_without_a_quotient_leaf() {
        let (body, challenges) = populated_wire();
        let wire = V8A100Wire::parse_for_schedule(
            &body,
            V8_A100_MAX_FRONTIER_FIXTURE,
            crate::v8_a100::V8_A100_FRONTIER_MAX_PER_TREE,
        )
        .unwrap();
        let original =
            v8_deep_quotients_optimized_wire(&wire, V8_A100_MAX_FRONTIER_FIXTURE, &challenges)
                .unwrap();

        let mut mutated = body;
        let query_start = crate::v8_a100::V8_A100_FIXED_PACKED_FIELD_BYTES
            + crate::v8_a100::V8_A100_ROOT_BYTES
            + crate::v6_onefold::V6_WORK_NONCE_BYTES;
        mutated[query_start] ^= 1;
        let wire = V8A100Wire::parse_for_schedule(
            &mutated,
            V8_A100_MAX_FRONTIER_FIXTURE,
            crate::v8_a100::V8_A100_FRONTIER_MAX_PER_TREE,
        )
        .unwrap();
        let changed =
            v8_deep_quotients_optimized_wire(&wire, V8_A100_MAX_FRONTIER_FIXTURE, &challenges)
                .unwrap();
        assert_ne!(changed, original);
    }

    #[test]
    fn direct_sampler_constant_remains_bounded_and_counter_free() {
        assert_eq!(V8_A100_MAX_QUERY_DRAWS, 64);
        assert_eq!(V8_A100_PROFILE_BINDING[28..30], [0, 0]);
    }
}
