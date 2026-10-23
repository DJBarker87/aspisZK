//! UNPROVED COST PROBE. Own D14 semantic prover; original prover unchanged.
use alloc::vec::Vec;
use aspis_core::{field::{WideExact, M31, QM31, P},Digest32,r0::{domain::Point,encoder::eval_message}};
use crate::r1_wire::{self as wire,Challenges,Error,SemanticTranscript};
use aspis_statement::{multilinear_evaluate_qm31,state_only_copy_helper_sum,StateOnlyTraceFoundation,pool_v1::{pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1,pair_forest_semantic_terminal::r0::Public,pair_forest_trace::PoolV1PairForestMergedC1CompilationV1}};
    #[derive(Clone, Copy)]
    pub enum Column<'a> {
        Base(&'a [M31; 1024]),
        Extension(&'a [QM31; 1024]),
    }
    /// Backend errors cause an abort, never a retry or a challenge filter.
    pub trait Commitments {
        fn c1(&mut self, columns: [Column<'_>; 27]) -> Result<[u8; 32], Error>;
        fn c2(&mut self, columns: [&[QM31; 1024]; 2]) -> Result<[u8; 32], Error>;
    }
    pub struct BuiltSemantics<H: Digest32> {
        pub bytes: Vec<u8>,
        pub transcript: SemanticTranscript<H>,
        pub challenges: Challenges,
        pub alpha: [QM31; 10],
        /// Opening integration starts with this row-25 state, bound roots,
        /// and the 25 challenges (not the later diagnostic row-27 state).
        pub state_before_z0: [u8; 32],
        pub roots: [[u8; 32]; 2],
        pub columns: [Vec<QM31>; 29],
        pub z: [aspis_core::circle::SecureCirclePoint; 2],
    }
    fn lift(x: M31) -> QM31 {
        QM31::from_cm31(aspis_core::field::CM31::from_m31(x))
    }
    pub fn point_claims(
        columns: &[Vec<QM31>; 29],
        point: &[QM31; 10],
    ) -> Result<[[QM31; 29]; 3], Error> {
        let mut claims = [[QM31::ZERO; 29]; 3];
        for (p, at) in wire::statement_points(point).iter().enumerate() {
            for (lane, column) in columns.iter().enumerate() {
                claims[p][lane] = multilinear_evaluate_qm31(column, at).ok_or(Error::Public)?;
            }
        }
        Ok(claims)
    }

    #[allow(clippy::too_many_arguments)]
    fn build_with_helper_mode<H: Digest32>(
        public: Public<'_>,
        c1: &[Vec<M31>; 26],
        d: &[QM31; 1024],
        g: &[QM31; 1024],
        h1_padding: &[QM31; 1024],
        helper: impl FnOnce(QM31, QM31) -> Result<Vec<QM31>, Error>,
        commitments: &mut impl Commitments,
        hash: H,
        variant: crate::transport::Variant,
    ) -> Result<BuiltSemantics<H>, Error> {
        // Reject raw noncanonical constructors rather than normalize their
        // commitment representation. D is supplied before any challenge.
        if c1
            .iter()
            .any(|v| v.len() != 1024 || v.iter().any(|x| x.0 >= P))
            || d.iter().chain(g).any(|x| {
                QM31::from_le_bytes(&{
                    let mut b = [0; 16];
                    x.write_le_bytes(&mut b);
                    b
                })
                .is_none()
            })
        {
            return Err(Error::Public);
        }
        let base: [&[M31; 1024]; 26] =
            core::array::from_fn(|i| c1[i].as_slice().try_into().unwrap());
        let first = core::array::from_fn(|i| {
            if i < 26 {
                Column::Base(base[i])
            } else {
                Column::Extension(d)
            }
        });
        let c1_root = commitments.c1(first)?;
        let mut transcript = SemanticTranscript::new(hash, &public.public_bytes().map_err(|_|Error::Public)?, &c1_root)?;
        let mut bytes = c1_root.to_vec();
        let mut scalar = |row, payload: &[u8], transcript: &mut SemanticTranscript<H>| {
            let framed = wire::record(row, payload)?;
            let value = transcript.semantic(row, &framed)?;
            bytes.extend_from_slice(&framed);
            Ok::<QM31, Error>(value)
        };
        let lambda = scalar(0, &[], &mut transcript)?;
        let chi = scalar(1, &[], &mut transcript)?;
        let mut h1 = helper(lambda, chi)?;
        aspis_prover::state_only_hiding::apply_pool_v1_pair_forest_h1_padding_mask_v1(
            &mut h1,
            h1_padding,
        )
        .map_err(|_| Error::Public)?;
        let h1: &[QM31; 1024] = h1.as_slice().try_into().map_err(|_| Error::Public)?;
        if state_only_copy_helper_sum(h1) != Some(QM31::ZERO) {
            return Err(Error::Public);
        }
        let c2_root = commitments.c2([h1, g])?;
        let theta = scalar(2, &c2_root, &mut transcript)?;
        let mut zc = [QM31::ZERO; 10];
        for (i, value) in zc.iter_mut().enumerate() {
            *value = scalar(3 + i as u8, &[], &mut transcript)?;
        }
        let mu = scalar(13, &[], &mut transcript)?;
        let columns: [Vec<QM31>; 29] = core::array::from_fn(|lane| match lane {
            0..=25 => c1[lane].iter().copied().map(lift).collect(),
            26 => h1.to_vec(),
            27 => g.to_vec(),
            _ => d.to_vec(),
        });
        let dc = variant.coefficients(d);
        let mut mask_sum = QM31::ZERO;
        for row in 0..1024 {
            let point = core::array::from_fn(|i| {
                if (row >> (9 - i)) & 1 == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                }
            });
            mask_sum = mask_sum.add(
                aspis_core::state_only_hiding::state_only_selected_mask_value(
                    &core::array::from_fn(|i| columns[i][row]),
                    &core::array::from_fn(|i| columns[16 + i][row]),
                    columns[27][row],
                    &point,
                ),
            );
        }
        for side in 0..2 {
            let h = &dc[28*side..28*(side+1)];
            mask_sum = mask_sum.add(h.iter().copied().fold(h[0], QM31::add).mul_m31(M31(512)));
        }
        let eta = scalar(
            14,
            &WideExact::from_qm31(mask_sum).to_le_bytes(),
            &mut transcript,
        )?;
        let challenges = Challenges {
            lambda,
            chi,
            theta,
            zc,
            mu,
            eta,
        };
        let (alpha, _) = crate::host_sumcheck::prove_sumcheck(
            &mut transcript,
            &mut bytes,
            mask_sum,
            |point| {
                let claims = point_claims(&columns, point)?;
                let terminal = public.terminal_qm31(&claims, point, &challenges).map_err(|_|Error::Public)?;
                let mask = aspis_core::state_only_hiding::state_only_selected_mask_value(
                    &core::array::from_fn(|i| claims[0][i]),
                    &core::array::from_fn(|i| claims[0][16 + i]),
                    claims[0][27],
                    point,
                );
                Ok(mask.add(eta.mul(terminal)).add(extra(&dc,point[8],point[9])))
            },
        )?;
        let claims = point_claims(&columns, &alpha)?;
        let state_before_z0 = transcript.state();
        let extras: [QM31;29] = core::array::from_fn(|l| {
            let rows: &[QM31;1024] = columns[l].as_slice().try_into().unwrap();
            extra(&variant.coefficients(rows),alpha[8],alpha[9])
        });
        let before_z0 = wire::record(
            25,
            &wire::encode_values(claims.into_iter().flatten().chain(extras).map(WideExact::from_qm31)),
        )?;
        let z0 = transcript.challenge_reference_circle_point(25, &before_z0)?;
        bytes.extend_from_slice(&before_z0);
        let endpoint = columns.iter().map(|col| {
            let message: &[QM31; 1024] = col.as_slice().try_into().unwrap();
            let coefficients = variant.coefficients(message);
            let message = &coefficients;
            WideExact::from_qm31(eval_message(message, Point { x: z0.x, y: z0.y }))
        });
        let before_z1 = wire::record(26, &wire::encode_values(endpoint))?;
        let z1 = transcript.challenge_reference_circle_point(26, &before_z1)?;
        bytes.extend_from_slice(&before_z1);
        if z0 == z1 {
            return Err(Error::EqualCirclePoints);
        }
        Ok(BuiltSemantics {
            bytes,
            transcript,
            challenges,
            alpha,
            state_before_z0,
            roots: [c1_root, c2_root],
            columns,
            z: [z0, z1],
        })
    }


pub fn extra(coefficients:&[QM31;1024],a:QM31,b:QM31)->QM31 {
    (0..2).fold(QM31::ZERO,|sum,s|sum.add(coefficients[s*28..s*28+28].iter().rev().fold(QM31::ZERO,|v,&c|v.mul(if s==0 {a}else{b}).add(c))))
}
pub fn build<H: Digest32>(public:Public<'_>,compiled:&PoolV1PairForestMergedC1CompilationV1,mask_only:&[Vec<M31>;10],d:&[QM31;1024],g:&[QM31;1024],commitments:&mut impl Commitments,hash:H,variant:crate::transport::Variant)->Result<BuiltSemantics<H>,Error> {
    if compiled.semantic_c1.c1.len()!=16 || &compiled.public_statement!=public.transition(){return Err(Error::Public);}
    let c1=core::array::from_fn(|i| if i<16 {compiled.semantic_c1.c1[i].clone()}else{mask_only[i-16].clone()});
    build_with_helper_mode(public,&c1,d,g,&[QM31::ZERO;1024],|lambda,chi|build_pool_v1_pair_forest_copy_helper_v1(&compiled.trace,public.transition().live_snapshot.next_pair_index,lambda,chi).map_err(|_|Error::Public),commitments,hash,variant)
}

/// Fixture-only entry for C1/H1 material from the existing state-only mask
/// APIs. The compiled trace remains the helper source; only the semantic C1
/// input is replaced with its independently masked clone.
pub fn build_with_material<H: Digest32>(
    public: Public<'_>,
    compiled: &PoolV1PairForestMergedC1CompilationV1,
    noised_semantic_c1: &StateOnlyTraceFoundation,
    mask_only: &[Vec<M31>; 10],
    d: &[QM31; 1024],
    g: &[QM31; 1024],
    h1_padding: &[QM31; 1024],
    commitments: &mut impl Commitments,
    hash: H,
    variant: crate::transport::Variant,
) -> Result<BuiltSemantics<H>, Error> {
    if noised_semantic_c1.c1.len() != 16
        || compiled.semantic_c1.c1.len() != 16
        || &compiled.public_statement != public.transition()
    {
        return Err(Error::Public);
    }
    let c1 = core::array::from_fn(|i| {
        if i < 16 {
            noised_semantic_c1.c1[i].clone()
        } else {
            mask_only[i - 16].clone()
        }
    });
    build_with_helper_mode(
        public,
        &c1,
        d,
        g,
        h1_padding,
        |lambda, chi| {
            #[cfg(feature = "r1p-check")]
            if !no_pole(compiled, lambda, chi)? {
                return Err(Error::ActivePole);
            }
            build_pool_v1_pair_forest_copy_helper_v1(
                &compiled.trace,
                public.transition().live_snapshot.next_pair_index,
                lambda,
                chi,
            )
            .map_err(|_| Error::Public)
        },
        commitments,
        hash,
        variant,
    )
}

/// Lean `NoPole (h.build w) λ χ` (R0Z/HonestValidity.lean:97–99), the `VR1`
/// conjunct of `realGameP` (R1Z/GamesR1P.lean:184): on every copy-active row,
/// chi differs from all four slot values (producer and consumer, slots 0 and
/// 1), whatever the slot's weight; an unused slot has value 0. The weighted
/// slots `build_copy_logup_helper` inverts are a subset, so this check is
/// stronger than its `ActivePole`. Only the verdict leaves this function.
#[cfg(feature = "r1p-check")]
pub(crate) fn no_pole(
    compiled: &PoolV1PairForestMergedC1CompilationV1,
    lambda: QM31,
    chi: QM31,
) -> Result<bool, Error> {
    #[cfg(test)]
    if crate::prover::test_hooks::forced_pole() {
        return Ok(false);
    }
    let values = lean_copy_row_values(&compiled.trace, lambda)?;
    let masks = aspis_statement::pool_v1::pool_v1_pair_forest_copy_active_row_masks_v1()
        .map_err(|_| Error::Public)?;
    let mut clear = true;
    for (row, sides) in values.iter().enumerate() {
        if masks[row >> 4] & (1 << (row & 15)) == 0 {
            continue;
        }
        for value in sides.iter().flatten() {
            // No early exit: the work done does not depend on where a pole is.
            clear &= chi != *value;
        }
    }
    Ok(clear)
}

/// Lean `copyRowValues t λ b endpoint slot` (v8-r0-sem-proof-20261008
/// lean/R0P/Copy.lean:449–452) for every row b, side (0 producer, 1 consumer)
/// and slot: the sum of the compressed tuples of the registry endpoints at
/// that row, side and static slot, weights ignored. The static slot is the
/// endpoint's position among the registry endpoints on the same row and side,
/// which is the slot of the generated terminal constants that the Lean
/// `copyLinks` transcribe (`retry_tests::static_slots_are_the_terminal_constants`).
/// The prover's `pool_v1_pair_forest_copy_rows_v1` cannot be used here: it
/// places an endpoint in the first slot whose weight is zero, so a zero-weight
/// endpoint followed by another on the same row and side is overwritten.
#[cfg(feature = "r1p-check")]
pub(crate) fn lean_copy_row_values(
    trace: &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,
    lambda: QM31,
) -> Result<Vec<[[QM31; 2]; 2]>, Error> {
    use aspis_statement::pool_v1::pair_trace::{PoolV1PairTraceBankV1, PoolV1PairTupleLimbV1};
    let registry = aspis_statement::pool_v1::pair_forest_trace::build_pool_v1_pair_forest_copy_registry_v1()
        .map_err(|_| Error::Public)?;
    let mut values = alloc::vec![[[QM31::ZERO; 2]; 2]; 1024];
    let mut arity = alloc::vec![[0usize; 2]; 1024];
    for link in registry {
        for (side, tuple) in [(0usize, link.producer), (1usize, link.consumer)] {
            let row = usize::from(tuple.row);
            if row >= 1024 || arity[row][side] >= 2 {
                return Err(Error::Public);
            }
            let slot = arity[row][side];
            arity[row][side] += 1;
            // The tuple read of pair_forest_trace.rs `tuple_value` (lines 580–591).
            let mut limbs = [M31::ZERO; 16];
            for (out, limb) in limbs.iter_mut().zip(tuple.limbs) {
                if let PoolV1PairTupleLimbV1::Cell { source, offset } = limb {
                    let columns = match source.bank {
                        PoolV1PairTraceBankV1::Stable => &trace.stable.c1,
                        PoolV1PairTraceBankV1::Late => &trace.late,
                    };
                    *out = columns
                        .get(source.cell.column as usize)
                        .and_then(|column| column.get(source.cell.row as usize))
                        .ok_or(Error::Public)?
                        .add(offset);
                }
            }
            values[row][side][slot] = values[row][side][slot]
                .add(aspis_statement::compress_tagged_tuple(link.tag, &limbs, lambda));
        }
    }
    Ok(values)
}
