//! UNPROVED COST PROBE. Isolated semantic interpolation prover.

    use alloc::vec::Vec;
    use aspis_core::field::{WideExact, CM31, M31, QM31};
    use crate::r1_wire::{self as wire, Error, SemanticTranscript};
    use aspis_core::state_only_sumcheck::{
        evaluate_state_only_polynomial, state_only_boundary_sum,
    };

    /// R0 keeps all 28 coefficients on the wire, embedded in E. This is the
    /// same interpolation used by the legacy prover, with a new row driver.
    fn interpolate(values: &[QM31; 28]) -> [QM31; 28] {
        let mut out = [QM31::ZERO; 28];
        for i in 0..28 {
            let mut basis = [M31::ZERO; 28];
            basis[0] = M31::ONE;
            let mut degree = 0;
            let mut denominator = M31::ONE;
            for j in 0..28 {
                if i == j {
                    continue;
                }
                for k in (0..=degree + 1).rev() {
                    let shifted = if k == 0 { M31::ZERO } else { basis[k - 1] };
                    basis[k] = shifted.sub(basis[k].mul(M31(j as u32)));
                }
                degree += 1;
                denominator = denominator.mul(M31(i as u32).sub(M31(j as u32)));
            }
            let scale = values[i].mul_m31(denominator.inv());
            for k in 0..28 {
                out[k] = out[k].add(scale.mul_m31(basis[k]));
            }
        }
        out
    }

    pub fn prove_sumcheck<H: aspis_core::Digest32>(
        transcript: &mut SemanticTranscript<H>,
        output: &mut Vec<u8>,
        initial_claim: QM31,
        mut oracle: impl FnMut(&[QM31; 10]) -> Result<QM31, Error>,
    ) -> Result<([QM31; 10], QM31), Error> {
        let mut point = [QM31::ZERO; 10];
        let mut running = initial_claim;
        for round in 0..10 {
            let remaining = 9 - round;
            let mut values = [QM31::ZERO; 28];
            for (sample, value) in values.iter_mut().enumerate() {
                point[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
                for assignment in 0..1usize << remaining {
                    for offset in 0..remaining {
                        point[round + 1 + offset] =
                            if (assignment >> (remaining - 1 - offset)) & 1 == 0 {
                                QM31::ZERO
                            } else {
                                QM31::ONE
                            };
                    }
                    *value = value.add(oracle(&point)?);
                }
            }
            let polynomial = interpolate(&values);
            if state_only_boundary_sum(&polynomial) != running {
                return Err(Error::Boundary { round });
            }
            let framed = wire::record(
                15 + round as u8,
                &wire::encode_values(polynomial.map(WideExact::from_qm31)),
            )?;
            point[round] = transcript.semantic(15 + round as u8, &framed)?;
            output.extend_from_slice(&framed);
            running = evaluate_state_only_polynomial(&polynomial, point[round]);
        }
        if oracle(&point)? != running {
            return Err(Error::Terminal);
        }
        Ok((point, running))
    }
