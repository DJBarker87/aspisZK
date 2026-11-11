//! UNPROVED COST PROBE. Isolated semantic interpolation prover.

    use alloc::vec::Vec;
    use aspis_core::field::{WideExact, CM31, M31, QM31};
    use crate::r1_wire::{self as wire, Error, SemanticTranscript};
    use aspis_core::state_only_sumcheck::{
        evaluate_state_only_polynomial, state_only_boundary_sum,
    };

    /// R0 keeps all 28 coefficients on the wire, embedded in E. This is the
    /// same interpolation used by the legacy prover, with a new row driver.
    pub(crate) fn interpolate(values: &[QM31; 28]) -> [QM31; 28] {
        let mut out = [QM31::ZERO; 28];
        let mut i = 0;
        while i < 28 {
            let mut basis = [M31::ZERO; 28];
            basis[0] = M31::ONE;
            let denominator = lagrange_basis(&mut basis, i);
            let scale = values[i].mul_m31(denominator.inv());
            accumulate_scaled(&mut out, &basis, scale);
            i += 1;
        }
        out
    }

    // Extraction helpers (pv-rw-b-20261110): the pinned loop nest of
    // `interpolate`, one counted loop per function, same arithmetic in the same
    // order. The conditional read `basis[k - 1]` lives in `basis_cell`: inline
    // in the k loop it is rejected by Aeneas (Internal error or 1991 crash).

    /// Multiplies `basis` by (X - j) for every j != i, in ascending j, and
    /// returns the product of (i - j) over the same j.
    fn lagrange_basis(basis: &mut [M31; 28], i: usize) -> M31 {
        let mut degree = 0;
        let mut denominator = M31::ONE;
        let mut j = 0;
        while j < 28 {
            if i != j {
                multiply_by_root(basis, degree, j);
                degree += 1;
                denominator = denominator.mul(M31(i as u32).sub(M31(j as u32)));
            }
            j += 1;
        }
        denominator
    }

    /// basis(X) := basis(X) * (X - j) for a basis of degree `degree`; cells
    /// k = degree + 1 down to 0, as in the pinned `(0..=degree + 1).rev()`.
    fn multiply_by_root(basis: &mut [M31; 28], degree: usize, j: usize) {
        let root = M31(j as u32);
        let mut k = degree + 2;
        while k > 0 {
            k -= 1;
            let next = basis_cell(basis, k, root);
            basis[k] = next;
        }
    }

    fn basis_cell(basis: &[M31; 28], k: usize, root: M31) -> M31 {
        let shifted = if k == 0 { M31::ZERO } else { basis[k - 1] };
        shifted.sub(basis[k].mul(root))
    }

    fn accumulate_scaled(out: &mut [QM31; 28], basis: &[M31; 28], scale: QM31) {
        let mut k = 0;
        while k < 28 {
            out[k] = out[k].add(scale.mul_m31(basis[k]));
            k += 1;
        }
    }

    pub fn prove_sumcheck<H: aspis_core::Digest32>(
        transcript: &mut SemanticTranscript<H>,
        output: &mut Vec<u8>,
        initial_claim: QM31,
        mut oracle: impl FnMut(&[QM31; 10]) -> Result<QM31, Error>,
    ) -> Result<([QM31; 10], QM31), Error> {
        let mut point = [QM31::ZERO; 10];
        let mut running = initial_claim;
        let mut round = 0;
        while round < 10 {
            running = prove_round(transcript, output, &mut point, running, round, &mut oracle)?;
            round += 1;
        }
        if oracle(&point)? != running {
            return Err(Error::Terminal);
        }
        Ok((point, running))
    }

    // Extraction helpers (pv-rw-b-20261110) for `prove_sumcheck`: the pinned
    // loop nest split into one counted loop per function, the oracle passed as
    // `&mut F`. Oracle call order, transcript/record order and first error are
    // the pinned ones.

    /// One sumcheck round: the 28 sample sums, the round polynomial, its
    /// boundary check, the framed record, the challenge and the new claim.
    fn prove_round<H: aspis_core::Digest32, F: FnMut(&[QM31; 10]) -> Result<QM31, Error>>(
        transcript: &mut SemanticTranscript<H>,
        output: &mut Vec<u8>,
        point: &mut [QM31; 10],
        running: QM31,
        round: usize,
        oracle: &mut F,
    ) -> Result<QM31, Error> {
        let values = round_values(point, round, oracle)?;
        let polynomial = interpolate(&values);
        if state_only_boundary_sum(&polynomial) != running {
            return Err(Error::Boundary { round });
        }
        let framed = wire::record(15 + round as u8, &wire::encode_values(wide_values(&polynomial)))?;
        point[round] = transcript.semantic(15 + round as u8, &framed)?;
        output.extend_from_slice(&framed);
        Ok(evaluate_state_only_polynomial(&polynomial, point[round]))
    }

    /// `polynomial.map(WideExact::from_qm31)` as a counted loop.
    fn wide_values(polynomial: &[QM31; 28]) -> [WideExact; 28] {
        let mut out = [WideExact::ZERO; 28];
        let mut i = 0;
        while i < 28 {
            out[i] = WideExact::from_qm31(polynomial[i]);
            i += 1;
        }
        out
    }

    /// Sample sums in sample order; the oracle is called in the pinned order
    /// and the first oracle error is returned unchanged.
    fn round_values<F: FnMut(&[QM31; 10]) -> Result<QM31, Error>>(
        point: &mut [QM31; 10],
        round: usize,
        oracle: &mut F,
    ) -> Result<[QM31; 28], Error> {
        let mut values = [QM31::ZERO; 28];
        let mut sample = 0;
        while sample < 28 {
            point[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
            values[sample] = sample_sum(point, round, oracle)?;
            sample += 1;
        }
        Ok(values)
    }

    /// Sum over the Boolean suffix assignments, in ascending assignment order.
    fn sample_sum<F: FnMut(&[QM31; 10]) -> Result<QM31, Error>>(
        point: &mut [QM31; 10],
        round: usize,
        oracle: &mut F,
    ) -> Result<QM31, Error> {
        let remaining = 9 - round;
        let mut value = QM31::ZERO;
        let mut assignment = 0;
        while assignment < 1usize << remaining {
            set_suffix(point, round, remaining, assignment);
            value = value.add(oracle(point)?);
            assignment += 1;
        }
        Ok(value)
    }

    fn set_suffix(point: &mut [QM31; 10], round: usize, remaining: usize, assignment: usize) {
        let mut offset = 0;
        while offset < remaining {
            point[round + 1 + offset] =
                if (assignment >> (remaining - 1 - offset)) & 1 == 0 { QM31::ZERO } else { QM31::ONE };
            offset += 1;
        }
    }

/// pv-rw-b-20261110: the pinned (4bb3b3f) bodies, kept verbatim under cfg(test)
/// so the rewritten bodies can be compared with them on random inputs.
#[cfg(test)]
mod lane_b_equivalence {
    use super::*;

    fn original_interpolate(values: &[QM31; 28]) -> [QM31; 28] {
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

    fn original_prove_sumcheck<H: aspis_core::Digest32>(
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
            let polynomial = original_interpolate(&values);
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

    struct Rng(u64);
    impl Rng {
        fn m31(&mut self) -> M31 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            M31(((self.0 >> 33) % 0x7fff_ffff) as u32)
        }
        fn qm31(&mut self) -> QM31 {
            QM31 { c0: CM31::new(self.m31(), self.m31()), c1: CM31::new(self.m31(), self.m31()) }
        }
    }

    #[derive(Clone, Copy)]
    struct TestDigest;
    impl aspis_core::Digest32 for TestDigest {
        fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
            // Deterministic non-cryptographic mixing, test only.
            let mut h = [0u8; 32];
            let mut acc = 0xcbf2_9ce4_8422_2325u64;
            for part in parts {
                for &b in *part {
                    acc = (acc ^ b as u64).wrapping_mul(0x100_0000_01b3);
                }
                acc = acc.rotate_left(17) ^ part.len() as u64;
            }
            for (i, c) in h.chunks_mut(8).enumerate() {
                acc = acc.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(i as u64);
                c.copy_from_slice(&acc.to_le_bytes());
            }
            h
        }
    }

    #[test]
    fn interpolate_matches_the_pinned_body() {
        let mut rng = Rng(0x5eed_0001);
        for _ in 0..64 {
            let values: [QM31; 28] = core::array::from_fn(|_| rng.qm31());
            assert_eq!(interpolate(&values), original_interpolate(&values));
        }
        let zero = [QM31::ZERO; 28];
        assert_eq!(interpolate(&zero), original_interpolate(&zero));
    }

    /// Oracle: an affine function of the point plus a degree-2 term in two
    /// coordinates, so every round polynomial has degree <= 2 and the honest
    /// claim passes every boundary check; `fail_at` makes call number k fail.
    fn affine_oracle(c: [QM31; 12], calls: &core::cell::Cell<usize>, fail_at: Option<usize>)
        -> impl FnMut(&[QM31; 10]) -> Result<QM31, Error> + '_ {
        move |p: &[QM31; 10]| {
            let k = calls.get();
            calls.set(k + 1);
            if fail_at == Some(k) {
                return Err(Error::Terminal);
            }
            let mut v = c[10];
            for i in 0..10 {
                v = v.add(c[i].mul(p[i]));
            }
            Ok(v.add(c[11].mul(p[2]).mul(p[7])))
        }
    }

    fn cube_sum(c: [QM31; 12]) -> QM31 {
        let calls = core::cell::Cell::new(0);
        let mut f = affine_oracle(c, &calls, None);
        let mut s = QM31::ZERO;
        for a in 0..1usize << 10 {
            let p: [QM31; 10] = core::array::from_fn(|i| if (a >> i) & 1 == 1 { QM31::ONE } else { QM31::ZERO });
            s = s.add(f(&p).unwrap());
        }
        s
    }

    fn run_pair(c: [QM31; 12], claim: QM31, fail_at: Option<usize>) {
        let root = [7u8; 32];
        let mut t_new = SemanticTranscript::new(TestDigest, b"public", &root).unwrap();
        let mut t_old = SemanticTranscript::new(TestDigest, b"public", &root).unwrap();
        // Advance both transcripts to row 15 identically (rows 0..14 precede the sumcheck).
        for row in 0..15u8 {
            let size = wire::row_shape(row).unwrap().1;
            let framed = wire::record(row, &alloc::vec![0; size]).unwrap();
            assert_eq!(t_new.semantic(row, &framed).unwrap(), t_old.semantic(row, &framed).unwrap());
        }
        let mut o_new = alloc::vec![1u8, 2, 3];
        let mut o_old = o_new.clone();
        let calls_new = core::cell::Cell::new(0);
        let calls_old = core::cell::Cell::new(0);
        let r_new = prove_sumcheck(&mut t_new, &mut o_new, claim, affine_oracle(c, &calls_new, fail_at));
        let r_old = original_prove_sumcheck(&mut t_old, &mut o_old, claim, affine_oracle(c, &calls_old, fail_at));
        assert_eq!(r_new, r_old);
        assert_eq!(o_new, o_old);
        assert_eq!(t_new.state(), t_old.state());
        assert_eq!(t_new.next_row(), t_old.next_row());
        assert_eq!(calls_new.get(), calls_old.get(), "same oracle call count");
    }

    #[test]
    fn prove_sumcheck_matches_the_pinned_body() {
        let mut rng = Rng(0x5eed_0002);
        for trial in 0..6 {
            let c: [QM31; 12] = core::array::from_fn(|_| rng.qm31());
            let claim = cube_sum(c);
            // honest claim: the full run succeeds
            run_pair(c, claim, None);
            // wrong claim: Boundary at round 0
            run_pair(c, claim.add(QM31::ONE), None);
            // oracle failure at several call positions (first call, mid-round, last round, terminal)
            let total = 28 * ((1usize << 10) - 1) + 1;
            for k in [0usize, 1, 513 + trial, 28 * 512 + 7, total - 2, total - 1] {
                run_pair(c, claim, Some(k));
            }
        }
    }
}
