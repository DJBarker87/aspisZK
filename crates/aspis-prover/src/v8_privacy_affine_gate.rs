//! Exact M31 certificates for fixed affine privacy subblocks.
//!
//! This research module can certify `im(T) subset im(M)` for source-derived
//! matrices. It cannot issue a publication permit: callers must separately
//! prove complete joint-view coverage, the conditional coin law, and a public
//! quotient for simulation.

use aspis_core::field::M31;

const MAX_ENTRIES: usize = 2_000_000;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AffineGateError {
    Ragged,
    ObservationMismatch,
    WorkspaceCap,
    InvalidCertificate,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AffineCertificate {
    Correction {
        rank: usize,
        matrix: Vec<Vec<M31>>,
    },
    Separator {
        rank: usize,
        lambda: Vec<M31>,
        target_column: usize,
        nonzero: M31,
    },
}

fn shape(matrix: &[Vec<M31>]) -> Result<(usize, usize), AffineGateError> {
    let columns = matrix.first().map_or(0, Vec::len);
    if matrix.iter().any(|row| row.len() != columns) {
        return Err(AffineGateError::Ragged);
    }
    Ok((matrix.len(), columns))
}

pub fn verify_fixed_affine_certificate(
    mask: &[Vec<M31>],
    target: &[Vec<M31>],
    certificate: &AffineCertificate,
) -> Result<(), AffineGateError> {
    let (rows, mask_columns) = shape(mask)?;
    let (target_rows, target_columns) = shape(target)?;
    if rows != target_rows {
        return Err(AffineGateError::ObservationMismatch);
    }
    match certificate {
        AffineCertificate::Correction { matrix, .. } => {
            if matrix.len() != mask_columns || matrix.iter().any(|row| row.len() != target_columns)
            {
                return Err(AffineGateError::InvalidCertificate);
            }
            for i in 0..rows {
                for j in 0..target_columns {
                    let value = (0..mask_columns)
                        .fold(M31::ZERO, |sum, k| sum.add(mask[i][k].mul(matrix[k][j])));
                    if value != target[i][j] {
                        return Err(AffineGateError::InvalidCertificate);
                    }
                }
            }
        }
        AffineCertificate::Separator {
            lambda,
            target_column,
            nonzero,
            ..
        } => {
            if lambda.len() != rows || *target_column >= target_columns || *nonzero == M31::ZERO {
                return Err(AffineGateError::InvalidCertificate);
            }
            for j in 0..mask_columns {
                let value = (0..rows).fold(M31::ZERO, |sum, i| sum.add(lambda[i].mul(mask[i][j])));
                if value != M31::ZERO {
                    return Err(AffineGateError::InvalidCertificate);
                }
            }
            let value = (0..rows).fold(M31::ZERO, |sum, i| {
                sum.add(lambda[i].mul(target[i][*target_column]))
            });
            if value != *nonzero {
                return Err(AffineGateError::InvalidCertificate);
            }
        }
    }
    Ok(())
}

pub fn certify_fixed_affine(
    mask: &[Vec<M31>],
    target: &[Vec<M31>],
) -> Result<AffineCertificate, AffineGateError> {
    let (rows, mask_columns) = shape(mask)?;
    let (target_rows, target_columns) = shape(target)?;
    if rows != target_rows {
        return Err(AffineGateError::ObservationMismatch);
    }
    if rows
        .checked_mul(mask_columns + target_columns + rows)
        .filter(|n| *n <= MAX_ENTRIES)
        .is_none()
    {
        return Err(AffineGateError::WorkspaceCap);
    }
    let mut a = mask.to_vec();
    let mut b = target.to_vec();
    let mut u = (0..rows)
        .map(|i| {
            (0..rows)
                .map(|j| if i == j { M31::ONE } else { M31::ZERO })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut pivots = Vec::new();
    let mut rank = 0usize;
    for column in 0..mask_columns {
        let Some(pivot) = (rank..rows).find(|&row| a[row][column] != M31::ZERO) else {
            continue;
        };
        a.swap(rank, pivot);
        b.swap(rank, pivot);
        u.swap(rank, pivot);
        let inverse = a[rank][column].inv();
        for value in &mut a[rank] {
            *value = value.mul(inverse);
        }
        for value in &mut b[rank] {
            *value = value.mul(inverse);
        }
        for value in &mut u[rank] {
            *value = value.mul(inverse);
        }
        for row in 0..rows {
            if row == rank || a[row][column] == M31::ZERO {
                continue;
            }
            let factor = a[row][column];
            let pivot_a = a[rank].clone();
            let pivot_b = b[rank].clone();
            let pivot_u = u[rank].clone();
            for j in column..mask_columns {
                a[row][j] = a[row][j].sub(factor.mul(pivot_a[j]));
            }
            for j in 0..target_columns {
                b[row][j] = b[row][j].sub(factor.mul(pivot_b[j]));
            }
            for j in 0..rows {
                u[row][j] = u[row][j].sub(factor.mul(pivot_u[j]));
            }
        }
        pivots.push(column);
        rank += 1;
        if rank == rows {
            break;
        }
    }
    for row in rank..rows {
        for column in 0..target_columns {
            if b[row][column] != M31::ZERO {
                let certificate = AffineCertificate::Separator {
                    rank,
                    lambda: u[row].clone(),
                    target_column: column,
                    nonzero: b[row][column],
                };
                verify_fixed_affine_certificate(mask, target, &certificate)?;
                return Ok(certificate);
            }
        }
    }
    let mut correction = vec![vec![M31::ZERO; target_columns]; mask_columns];
    for (row, &column) in pivots.iter().enumerate() {
        correction[column].copy_from_slice(&b[row]);
    }
    let certificate = AffineCertificate::Correction {
        rank,
        matrix: correction,
    };
    verify_fixed_affine_certificate(mask, target, &certificate)?;
    Ok(certificate)
}

/// Certify earlier and later affine observations with the same coin vector.
/// The earlier target must contain its real witness offset; replacing it by
/// zero is sound only when that offset is already proved equal.
pub fn certify_joint_affine(
    earlier_mask: &[Vec<M31>],
    later_mask: &[Vec<M31>],
    earlier_target: &[Vec<M31>],
    later_target: &[Vec<M31>],
) -> Result<AffineCertificate, AffineGateError> {
    let (_, earlier_mask_columns) = shape(earlier_mask)?;
    let (_, later_mask_columns) = shape(later_mask)?;
    let (_, earlier_target_columns) = shape(earlier_target)?;
    let (_, later_target_columns) = shape(later_target)?;
    if earlier_mask_columns != later_mask_columns || earlier_target_columns != later_target_columns
    {
        return Err(AffineGateError::ObservationMismatch);
    }
    let mut mask = earlier_mask.to_vec();
    mask.extend_from_slice(later_mask);
    let mut target = earlier_target.to_vec();
    target.extend_from_slice(later_target);
    certify_fixed_affine(&mask, &target)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circle_candidate::CircleEncoder;
    use aspis_statement::pool_v1::{
        pool_v1_pair_forest_copy_active_rows_v1, pool_v1_pair_forest_relation_free_mask_cells_v1,
    };

    const GROUPS: [usize; 128] = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
        48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 2736, 3392, 3786, 5472,
        6322, 8127, 8854, 9309, 10801, 12501, 13757, 13806, 14031, 15316, 16953, 19322, 20535,
        21839, 22933, 23948, 24425, 24460, 24679, 26011, 26619, 27618, 28210, 29819, 30111, 31624,
        32233, 32392, 32744, 33723, 34554, 34822, 35598, 38386, 40760, 40834, 43862, 45175, 45230,
        45479, 46521, 47261, 47292, 51488, 51803, 52786, 53396, 54007, 54734, 55904, 56566, 57014,
        57391, 58648, 59282, 59498, 60265, 60478, 60856, 63826,
    ];

    fn raw_mask(encoder: &CircleEncoder, queries: &[usize], column: usize) -> Vec<Vec<M31>> {
        let active = pool_v1_pair_forest_copy_active_rows_v1().unwrap();
        let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
        let available = cells
            .iter()
            .filter(|cell| {
                usize::from(cell.column) == column
                    && usize::from(cell.row) != 1023
                    && !(column == 3 && usize::from(cell.row) == 1014)
            })
            .map(|cell| usize::from(cell.row))
            .collect::<Vec<_>>();
        let mut mask = Vec::new();
        for &query in queries {
            for slot in 0..4 {
                let index = 4 * query + slot;
                let dependent = encoder.encode_c1_basis_value(1023, index).unwrap();
                mask.push(
                    available
                        .iter()
                        .map(|&row| {
                            let value = encoder.encode_c1_basis_value(row, index).unwrap();
                            if active.contains(&(row as u16)) {
                                value
                            } else {
                                value.sub(dependent)
                            }
                        })
                        .collect(),
                );
            }
        }
        mask
    }

    fn raw_map(
        encoder: &CircleEncoder,
        queries: &[usize],
        column: usize,
        target_row: usize,
    ) -> (Vec<Vec<M31>>, Vec<Vec<M31>>) {
        let mask = raw_mask(encoder, queries, column);
        let target = queries
            .iter()
            .flat_map(|query| (0..4).map(move |slot| 4 * query + slot))
            .map(|index| vec![encoder.encode_c1_basis_value(target_row, index).unwrap()])
            .collect();
        (mask, target)
    }

    #[test]
    fn marginal_pass_can_fail_jointly() {
        let one = vec![vec![M31::ONE]];
        assert!(matches!(
            certify_fixed_affine(&one, &one).unwrap(),
            AffineCertificate::Correction { .. }
        ));
        let zero = vec![vec![M31::ZERO]];
        assert!(matches!(
            certify_joint_affine(&one, &one, &zero, &one).unwrap(),
            AffineCertificate::Separator { .. }
        ));
    }

    #[test]
    fn earlier_witness_offset_is_not_zeroed() {
        let one = vec![vec![M31::ONE]];
        let zero = vec![vec![M31::ZERO]];
        assert!(matches!(
            certify_joint_affine(&one, &one, &one, &one).unwrap(),
            AffineCertificate::Correction { .. }
        ));
        assert!(matches!(
            certify_joint_affine(&one, &one, &zero, &one).unwrap(),
            AffineCertificate::Separator { .. }
        ));
    }

    #[test]
    fn harmless_rank_deficiency_and_corrupt_certificate_controls() {
        let mask = vec![vec![M31::ONE], vec![M31::ONE]];
        let target = vec![vec![M31(2)], vec![M31(2)]];
        assert!(matches!(
            certify_fixed_affine(&mask, &target).unwrap(),
            AffineCertificate::Correction { rank: 1, .. }
        ));
        let corrupt = AffineCertificate::Correction {
            rank: 1,
            matrix: vec![vec![M31::ZERO]],
        };
        assert_eq!(
            verify_fixed_affine_certificate(&mask, &target, &corrupt),
            Err(AffineGateError::InvalidCertificate)
        );
    }

    #[test]
    fn published_pair_certificates_reproduce() {
        let encoder = CircleEncoder::new_for_domain_log(20);
        for (queries, column, row, lambda, expected) in [
            (
                [4, 6],
                0,
                913,
                [
                    1508290849, 1480589898, 639192798, 666893749, 2147483646, 0, 1, 0,
                ],
                M31(490597912),
            ),
            (
                [1, 2],
                3,
                1014,
                [
                    1716687237, 1731393124, 430796410, 416090523, 1986164149, 0, 161319498, 0,
                ],
                M31::ONE,
            ),
        ] {
            let (mask, target) = raw_map(&encoder, &queries, column, row);
            let published = AffineCertificate::Separator {
                rank: 0,
                lambda: lambda.into_iter().map(M31).collect(),
                target_column: 0,
                nonzero: expected,
            };
            verify_fixed_affine_certificate(&mask, &target, &published).unwrap();
            let certificate = certify_fixed_affine(&mask, &target).unwrap();
            verify_fixed_affine_certificate(&mask, &target, &certificate).unwrap();
            match certificate {
                AffineCertificate::Separator { nonzero, .. } => assert_ne!(nonzero, M31::ZERO),
                _ => panic!("known separator unexpectedly passed"),
            }
        }
    }

    #[test]
    fn predeclared_768_pair_family_fails_raw_column_zero_gate() {
        let encoder = CircleEncoder::new_for_domain_log(20);
        let mut checked = 0usize;
        for group in GROUPS {
            for first in 0..4 {
                for second in first + 1..4 {
                    let queries = [4 * group + first, 4 * group + second];
                    let (mask, target) = raw_map(&encoder, &queries, 0, 913);
                    let certificate = certify_fixed_affine(&mask, &target).unwrap();
                    verify_fixed_affine_certificate(&mask, &target, &certificate).unwrap();
                    assert!(
                        matches!(certificate, AffineCertificate::Separator { .. }),
                        "pair {queries:?} unexpectedly passed"
                    );
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 768);
    }

    #[test]
    fn source_locked_complete_schedule_raw_controls() {
        let encoder = CircleEncoder::new_for_domain_log(20);
        let spread = (0..22).map(|i| 11915 * i).collect::<Vec<_>>();
        let identity = (0..88)
            .map(|i| {
                (0..88)
                    .map(|j| if i == j { M31::ONE } else { M31::ZERO })
                    .collect()
            })
            .collect::<Vec<Vec<M31>>>();
        for column in 0..16 {
            let mask = raw_mask(&encoder, &spread, column);
            assert!(matches!(
                certify_fixed_affine(&mask, &identity).unwrap(),
                AffineCertificate::Correction { rank: 88, .. }
            ));
        }

        let scattered = [
            4, 6, 103685, 223415, 21813, 185513, 212496, 16679, 187089, 157035, 195744, 244899,
            19086, 92907, 159274, 218276, 18837, 12291, 224498, 187006, 38787, 56305,
        ];
        let (mask, target) = raw_map(&encoder, &scattered, 0, 913);
        assert!(matches!(
            certify_fixed_affine(&mask, &target).unwrap(),
            AffineCertificate::Separator { rank: 86, .. }
        ));
    }
}
