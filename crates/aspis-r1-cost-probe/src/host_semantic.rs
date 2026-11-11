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
    /// pv-rw-c (extraction rewrite): counted loops instead of enumerate
    /// iterators; same evaluation order (point-major, then lane) and the same
    /// first-failure `Err(Error::Public)` exit as the original.
    pub fn point_claims(
        columns: &[Vec<QM31>; 29],
        point: &[QM31; 10],
    ) -> Result<[[QM31; 29]; 3], Error> {
        let points = wire::statement_points(point);
        let p0 = lane_claims(columns, &points[0])?;
        let p1 = lane_claims(columns, &points[1])?;
        let p2 = lane_claims(columns, &points[2])?;
        Ok([p0, p1, p2])
    }

    /// pv-rw-c: the 29 lane evaluations at one statement point, lanes in
    /// order; the first `None` is `Err(Error::Public)`.
    fn lane_claims(columns: &[Vec<QM31>; 29], at: &[QM31; 10]) -> Result<[QM31; 29], Error> {
        let mut out = [QM31::ZERO; 29];
        let mut lane = 0;
        while lane < 29 {
            match multilinear_evaluate_qm31(&columns[lane], at) {
                Some(value) => out[lane] = value,
                None => return Err(Error::Public),
            }
            lane += 1;
        }
        Ok(out)
    }

    /// pv-rw-c: the former `scalar` closure of `build_with_helper_mode`, with
    /// its captured `bytes` passed explicitly. Same record, transcript call
    /// and append order.
    fn semantic_scalar<H: Digest32>(
        bytes: &mut Vec<u8>,
        transcript: &mut SemanticTranscript<H>,
        row: u8,
        payload: &[u8],
    ) -> Result<QM31, Error> {
        let framed = wire::record(row, payload)?;
        let value = transcript.semantic(row, &framed)?;
        bytes.extend_from_slice(&framed);
        Ok(value)
    }

    /// pv-rw-c: the canonicality test of a QM31 (the former closure body).
    fn qm31_noncanonical(x: &QM31) -> bool {
        let mut b = [0; 16];
        x.write_le_bytes(&mut b);
        QM31::from_le_bytes(&b).is_none()
    }

    /// pv-rw-c: the input rejection of `build_with_helper_mode`, with the
    /// same short-circuit order as the original `any` chain (c1 columns in
    /// order, length before values; then d, then g).
    fn noncanonical_inputs(c1: &[Vec<M31>; 26], d: &[QM31; 1024], g: &[QM31; 1024]) -> bool {
        let mut i = 0;
        while i < 26 {
            let v = &c1[i];
            if v.len() != 1024 {
                return true;
            }
            let mut j = 0;
            while j < v.len() {
                if v[j].0 >= P {
                    return true;
                }
                j += 1;
            }
            i += 1;
        }
        let mut j = 0;
        while j < 1024 {
            if qm31_noncanonical(&d[j]) {
                return true;
            }
            j += 1;
        }
        let mut j = 0;
        while j < 1024 {
            if qm31_noncanonical(&g[j]) {
                return true;
            }
            j += 1;
        }
        false
    }

    /// pv-rw-c: `c1[i].as_slice().try_into().unwrap()` (the former closure).
    fn as_rows(v: &Vec<M31>) -> &[M31; 1024] {
        v.as_slice().try_into().unwrap()
    }

    /// pv-rw-c: the first commitment's 27 columns (26 base, then d), as an
    /// array literal instead of `from_fn`.
    fn first_columns<'a>(c1: &'a [Vec<M31>; 26], d: &'a [QM31; 1024]) -> [Column<'a>; 27] {
        [
            Column::Base(as_rows(&c1[0])), Column::Base(as_rows(&c1[1])), Column::Base(as_rows(&c1[2])),
            Column::Base(as_rows(&c1[3])), Column::Base(as_rows(&c1[4])), Column::Base(as_rows(&c1[5])),
            Column::Base(as_rows(&c1[6])), Column::Base(as_rows(&c1[7])), Column::Base(as_rows(&c1[8])),
            Column::Base(as_rows(&c1[9])), Column::Base(as_rows(&c1[10])), Column::Base(as_rows(&c1[11])),
            Column::Base(as_rows(&c1[12])), Column::Base(as_rows(&c1[13])), Column::Base(as_rows(&c1[14])),
            Column::Base(as_rows(&c1[15])), Column::Base(as_rows(&c1[16])), Column::Base(as_rows(&c1[17])),
            Column::Base(as_rows(&c1[18])), Column::Base(as_rows(&c1[19])), Column::Base(as_rows(&c1[20])),
            Column::Base(as_rows(&c1[21])), Column::Base(as_rows(&c1[22])), Column::Base(as_rows(&c1[23])),
            Column::Base(as_rows(&c1[24])), Column::Base(as_rows(&c1[25])),
            Column::Extension(d),
        ]
    }

    /// pv-rw-c: `c1[lane].iter().copied().map(lift).collect()`.
    fn lift_column(v: &Vec<M31>) -> Vec<QM31> {
        let mut out = Vec::with_capacity(v.len());
        let mut j = 0;
        while j < v.len() {
            out.push(lift(v[j]));
            j += 1;
        }
        out
    }

    /// pv-rw-c: the 29 semantic columns (26 lifted C1, h1, g, d) as an array
    /// literal instead of `from_fn` with a `match`.
    fn semantic_columns(
        c1: &[Vec<M31>; 26],
        h1: &[QM31; 1024],
        g: &[QM31; 1024],
        d: &[QM31; 1024],
    ) -> [Vec<QM31>; 29] {
        [
            lift_column(&c1[0]), lift_column(&c1[1]), lift_column(&c1[2]), lift_column(&c1[3]),
            lift_column(&c1[4]), lift_column(&c1[5]), lift_column(&c1[6]), lift_column(&c1[7]),
            lift_column(&c1[8]), lift_column(&c1[9]), lift_column(&c1[10]), lift_column(&c1[11]),
            lift_column(&c1[12]), lift_column(&c1[13]), lift_column(&c1[14]), lift_column(&c1[15]),
            lift_column(&c1[16]), lift_column(&c1[17]), lift_column(&c1[18]), lift_column(&c1[19]),
            lift_column(&c1[20]), lift_column(&c1[21]), lift_column(&c1[22]), lift_column(&c1[23]),
            lift_column(&c1[24]), lift_column(&c1[25]),
            h1.to_vec(),
            g.to_vec(),
            d.to_vec(),
        ]
    }

    /// pv-rw-c: the selected-mask value of one trace row (the body of the
    /// former row loop, with its three `from_fn` closures as counted loops).
    fn row_mask_value(columns: &[Vec<QM31>; 29], row: usize) -> QM31 {
        let mut point = [QM31::ZERO; 10];
        let mut i = 0;
        while i < 10 {
            if (row >> (9 - i)) & 1 != 0 {
                point[i] = QM31::ONE;
            }
            i += 1;
        }
        let mut c1 = [QM31::ZERO; 16];
        let mut i = 0;
        while i < 16 {
            c1[i] = columns[i][row];
            i += 1;
        }
        let mut mask_only = [QM31::ZERO; 10];
        let mut i = 0;
        while i < 10 {
            mask_only[i] = columns[16 + i][row];
            i += 1;
        }
        aspis_core::state_only_hiding::state_only_selected_mask_value(
            &c1,
            &mask_only,
            columns[27][row],
            &point,
        )
    }

    /// pv-rw-c: the row part of the mask sum (rows 0..1024 in order).
    fn rows_mask_sum(columns: &[Vec<QM31>; 29]) -> QM31 {
        let mut mask_sum = QM31::ZERO;
        let mut row = 0;
        while row < 1024 {
            mask_sum = mask_sum.add(row_mask_value(columns, row));
            row += 1;
        }
        mask_sum
    }

    /// pv-rw-c: `h.iter().copied().fold(h[0], QM31::add)` for the 28
    /// coefficients of one side (side * 28 .. side * 28 + 28).
    fn side_fold(dc: &[QM31; 1024], side: usize) -> QM31 {
        let h = &dc[28 * side..28 * (side + 1)];
        add_all(h[0], h)
    }

    /// pv-rw-c: `h.iter().copied().fold(seed, QM31::add)` as a counted loop.
    fn add_all(seed: QM31, h: &[QM31]) -> QM31 {
        let mut acc = seed;
        let mut j = 0;
        while j < h.len() {
            acc = acc.add(h[j]);
            j += 1;
        }
        acc
    }

    /// pv-rw-c: the per-column extras of row 25 (the former `from_fn`).
    fn column_extras(
        columns: &[Vec<QM31>; 29],
        variant: crate::transport::Variant,
        a: QM31,
        b: QM31,
    ) -> [QM31; 29] {
        let mut out = [QM31::ZERO; 29];
        let mut l = 0;
        while l < 29 {
            let rows: &[QM31; 1024] = columns[l].as_slice().try_into().unwrap();
            out[l] = extra(&variant.coefficients(rows), a, b);
            l += 1;
        }
        out
    }

    /// pv-rw-c: the row-25 values, `claims` flattened point-major and then the
    /// extras, as one array in the same order as the original iterator chain.
    fn before_z0_values(claims: &[[QM31; 29]; 3], extras: &[QM31; 29]) -> [WideExact; 116] {
        let mut out = [WideExact::default(); 116];
        let mut p = 0;
        while p < 3 {
            let mut lane = 0;
            while lane < 29 {
                out[29 * p + lane] = WideExact::from_qm31(claims[p][lane]);
                lane += 1;
            }
            p += 1;
        }
        let mut lane = 0;
        while lane < 29 {
            out[87 + lane] = WideExact::from_qm31(extras[lane]);
            lane += 1;
        }
        out
    }

    /// pv-rw-c: the row-26 endpoint values at z0 (the former `map` closure).
    fn endpoint_values(
        columns: &[Vec<QM31>; 29],
        variant: crate::transport::Variant,
        z: Point<QM31>,
    ) -> [WideExact; 29] {
        let mut out = [WideExact::default(); 29];
        let mut l = 0;
        while l < 29 {
            let message: &[QM31; 1024] = columns[l].as_slice().try_into().unwrap();
            let coefficients = variant.coefficients(message);
            out[l] = WideExact::from_qm31(eval_message(&coefficients, z));
            l += 1;
        }
        out
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
        if noncanonical_inputs(c1, d, g) {
            return Err(Error::Public);
        }
        let first = first_columns(c1, d);
        let c1_root = commitments.c1(first)?;
        let mut transcript = SemanticTranscript::new(hash, &public.public_bytes().map_err(|_|Error::Public)?, &c1_root)?;
        let mut bytes = c1_root.to_vec();
        let lambda = semantic_scalar(&mut bytes, &mut transcript, 0, &[])?;
        let chi = semantic_scalar(&mut bytes, &mut transcript, 1, &[])?;
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
        let theta = semantic_scalar(&mut bytes, &mut transcript, 2, &c2_root)?;
        // pv-rw-c: rows 3..13 unrolled (the former counted loop), in order.
        let z3 = semantic_scalar(&mut bytes, &mut transcript, 3, &[])?;
        let z4 = semantic_scalar(&mut bytes, &mut transcript, 4, &[])?;
        let z5 = semantic_scalar(&mut bytes, &mut transcript, 5, &[])?;
        let z6 = semantic_scalar(&mut bytes, &mut transcript, 6, &[])?;
        let z7 = semantic_scalar(&mut bytes, &mut transcript, 7, &[])?;
        let z8 = semantic_scalar(&mut bytes, &mut transcript, 8, &[])?;
        let z9 = semantic_scalar(&mut bytes, &mut transcript, 9, &[])?;
        let z10 = semantic_scalar(&mut bytes, &mut transcript, 10, &[])?;
        let z11 = semantic_scalar(&mut bytes, &mut transcript, 11, &[])?;
        let z12 = semantic_scalar(&mut bytes, &mut transcript, 12, &[])?;
        let zc = [z3, z4, z5, z6, z7, z8, z9, z10, z11, z12];
        let mu = semantic_scalar(&mut bytes, &mut transcript, 13, &[])?;
        let columns = semantic_columns(c1, h1, g, d);
        let dc = variant.coefficients(d);
        let mut mask_sum = rows_mask_sum(&columns);
        mask_sum = mask_sum.add(side_fold(&dc, 0).mul_m31(M31(512)));
        mask_sum = mask_sum.add(side_fold(&dc, 1).mul_m31(M31(512)));
        let eta = semantic_scalar(
            &mut bytes,
            &mut transcript,
            14,
            &WideExact::from_qm31(mask_sum).to_le_bytes(),
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
        let extras = column_extras(&columns, variant, alpha[8], alpha[9]);
        let before_z0 = wire::record(
            25,
            &wire::encode_values(before_z0_values(&claims, &extras)),
        )?;
        let z0 = transcript.challenge_reference_circle_point(25, &before_z0)?;
        bytes.extend_from_slice(&before_z0);
        let endpoint = endpoint_values(&columns, variant, Point { x: z0.x, y: z0.y });
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
    // pv-rw-c: counted loops instead of enumerate/flatten; same rows, the
    // same public active-row test, and every slot of an active row visited.
    Ok(rows_clear(&values, &masks, chi))
}

/// pv-rw-c: `chi` differs from all four slot values of one row (producer
/// slots 0, 1, then consumer slots 0, 1, the order of `iter().flatten()`).
/// No early exit: the work done does not depend on where a pole is.
/// pv-rw-c: the conjunction over all rows in order (no early exit).
#[cfg(feature = "r1p-check")]
fn rows_clear(values: &Vec<[[QM31; 2]; 2]>, masks: &[u16; 64], chi: QM31) -> bool {
    let mut clear = true;
    let mut row = 0;
    while row < values.len() {
        clear &= masked_row_clear(masks, &values[row], row, chi);
        row += 1;
    }
    clear
}

/// pv-rw-c: `row_clear` on a copy-active row; `true` (no effect on the
/// conjunction) on an inactive one. The activity mask is public.
#[cfg(feature = "r1p-check")]
fn masked_row_clear(masks: &[u16; 64], sides: &[[QM31; 2]; 2], row: usize, chi: QM31) -> bool {
    if masks[row >> 4] & (1 << (row & 15)) == 0 {
        return true;
    }
    row_clear(sides, chi)
}

#[cfg(feature = "r1p-check")]
fn row_clear(sides: &[[QM31; 2]; 2], chi: QM31) -> bool {
    let mut clear = true;
    let mut side = 0;
    while side < 2 {
        let mut slot = 0;
        while slot < 2 {
            clear &= chi != sides[side][slot];
            slot += 1;
        }
        side += 1;
    }
    clear
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
    let registry = aspis_statement::pool_v1::pair_forest_trace::build_pool_v1_pair_forest_copy_registry_v1()
        .map_err(|_| Error::Public)?;
    let mut values = alloc::vec![[[QM31::ZERO; 2]; 2]; 1024];
    let mut arity = alloc::vec![[0usize; 2]; 1024];
    // pv-rw-c: counted loops; links in registry order, producer (side 0)
    // before consumer (side 1), the same checks and the same first error.
    let mut k = 0;
    while k < registry.len() {
        let link = registry[k];
        add_copy_endpoint(trace, &mut values, &mut arity, 0, &link.producer, link.tag, lambda)?;
        add_copy_endpoint(trace, &mut values, &mut arity, 1, &link.consumer, link.tag, lambda)?;
        k += 1;
    }
    Ok(values)
}

/// pv-rw-c: one endpoint of `lean_copy_row_values` (the former inner loop
/// body): arity check, static slot, tuple read, compressed-tuple sum.
#[cfg(feature = "r1p-check")]
#[allow(clippy::too_many_arguments)]
fn add_copy_endpoint(
    trace: &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,
    values: &mut Vec<[[QM31; 2]; 2]>,
    arity: &mut Vec<[usize; 2]>,
    side: usize,
    tuple: &aspis_statement::pool_v1::pair_trace::PoolV1PairCopyTupleV1,
    tag: M31,
    lambda: QM31,
) -> Result<(), Error> {
    let row = usize::from(tuple.row);
    if row >= 1024 || arity[row][side] >= 2 {
        return Err(Error::Public);
    }
    let slot = arity[row][side];
    arity[row][side] += 1;
    let limbs = tuple_limbs(trace, tuple)?;
    values[row][side][slot] = values[row][side][slot]
        .add(aspis_statement::compress_tagged_tuple(tag, &limbs, lambda));
    Ok(())
}

/// pv-rw-c: the tuple read of pair_forest_trace.rs `tuple_value` (lines
/// 580–591), limb by limb in order; the first missing cell is `Error::Public`.
#[cfg(feature = "r1p-check")]
fn tuple_limbs(
    trace: &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,
    tuple: &aspis_statement::pool_v1::pair_trace::PoolV1PairCopyTupleV1,
) -> Result<[M31; 16], Error> {
    // Unrolled (limb 0..15 in order); the first missing cell is the error.
    let l = &tuple.limbs;
    Ok([
        limb_value(trace, l[0])?, limb_value(trace, l[1])?, limb_value(trace, l[2])?, limb_value(trace, l[3])?,
        limb_value(trace, l[4])?, limb_value(trace, l[5])?, limb_value(trace, l[6])?, limb_value(trace, l[7])?,
        limb_value(trace, l[8])?, limb_value(trace, l[9])?, limb_value(trace, l[10])?, limb_value(trace, l[11])?,
        limb_value(trace, l[12])?, limb_value(trace, l[13])?, limb_value(trace, l[14])?, limb_value(trace, l[15])?,
    ])
}

/// pv-rw-c: one limb, taken by value: `Zero` keeps the initial `M31::ZERO`,
/// `Cell` is the cell plus its offset, a missing cell is `Error::Public`.
#[cfg(feature = "r1p-check")]
fn limb_value(
    trace: &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,
    limb: aspis_statement::pool_v1::pair_trace::PoolV1PairTupleLimbV1,
) -> Result<M31, Error> {
    use aspis_statement::pool_v1::pair_trace::PoolV1PairTupleLimbV1;
    match limb {
        PoolV1PairTupleLimbV1::Zero => Ok(M31::ZERO),
        PoolV1PairTupleLimbV1::Cell { source, offset } => match trace_cell(trace, &source) {
            Some(value) => Ok(value.add(offset)),
            None => Err(Error::Public),
        },
    }
}

/// pv-rw-c: `columns.get(column).and_then(|c| c.get(row))` on the bank's
/// columns, as explicit bounds checks.
#[cfg(feature = "r1p-check")]
fn trace_cell(
    trace: &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,
    source: &aspis_statement::pool_v1::pair_trace::PoolV1PairTraceCellV1,
) -> Option<M31> {
    use aspis_statement::pool_v1::pair_trace::PoolV1PairTraceBankV1;
    let column = source.cell.column as usize;
    let row = source.cell.row as usize;
    match source.bank {
        PoolV1PairTraceBankV1::Stable => bank_cell(&trace.stable.c1, column, row),
        PoolV1PairTraceBankV1::Late => bank_cell(&trace.late, column, row),
    }
}

/// pv-rw-c: `columns.get(column).and_then(|c| c.get(row)).copied()` on one
/// 16-column bank, as explicit bounds checks.
#[cfg(feature = "r1p-check")]
fn bank_cell(columns: &[Vec<M31>; 16], column: usize, row: usize) -> Option<M31> {
    if column >= 16 {
        return None;
    }
    if row >= columns[column].len() {
        return None;
    }
    Some(columns[column][row])
}

/// pv-rw-c differential tests: the pinned (4bb3b3f51e) bodies of every
/// rewritten function, kept verbatim except for visibility and names, against
/// the rewritten ones. Unit-level evidence only; byte identity of whole proofs
/// is NOT tested here.
#[cfg(test)]
mod pv_rw_c_original {
    use super::*;
    use aspis_core::field::CM31;
    pub(super) fn point_claims(
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
    pub(super) fn build_with_helper_mode<H: Digest32>(
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


    #[cfg(feature = "r1p-check")]
    pub(super) fn no_pole(
        compiled: &PoolV1PairForestMergedC1CompilationV1,
        lambda: QM31,
        chi: QM31,
    ) -> Result<bool, Error> {
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

    #[cfg(feature = "r1p-check")]
    pub(super) fn lean_copy_row_values(
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

    /// The pinned row-mask loop and side folds of build_with_helper_mode
    /// (lines 116-137 at the pin), as a function of the columns and dc.
    pub(super) fn mask_sum_orig(columns: &[Vec<QM31>; 29], dc: &[QM31; 1024]) -> QM31 {
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
        mask_sum
    }

    pub(super) fn noncanonical_orig(c1: &[Vec<M31>; 26], d: &[QM31; 1024], g: &[QM31; 1024]) -> bool {
        c1
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
    }

    /// Deterministic xorshift64* generator (no new dependency).
    pub(super) struct Rng(pub u64);
    impl Rng {
        pub fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_f491_4f6c_dd1d)
        }
        pub fn m31(&mut self) -> M31 {
            M31((self.next() % (P as u64)) as u32)
        }
        pub fn qm31(&mut self) -> QM31 {
            QM31 { c0: CM31::new(self.m31(), self.m31()), c1: CM31::new(self.m31(), self.m31()) }
        }
    }
}

#[cfg(test)]
mod pv_rw_c_tests {
    use super::*;
    use super::pv_rw_c_original as orig;
    use orig::Rng;

    fn random_columns(rng: &mut Rng) -> [Vec<QM31>; 29] {
        core::array::from_fn(|_| (0..1024).map(|_| rng.qm31()).collect())
    }

    #[test]
    fn point_claims_matches_pinned() {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        for _ in 0..3 {
            let columns = random_columns(&mut rng);
            let point: [QM31; 10] = core::array::from_fn(|_| rng.qm31());
            assert_eq!(point_claims(&columns, &point), orig::point_claims(&columns, &point));
            let mut short = columns.clone();
            short[7].pop();
            assert_eq!(point_claims(&short, &point), orig::point_claims(&short, &point));
            assert_eq!(point_claims(&short, &point), Err(Error::Public));
        }
    }

    #[test]
    fn mask_sum_and_column_helpers_match_pinned() {
        let mut rng = Rng(0x1234_5678_9abc_def1);
        for variant in [crate::transport::Variant::S1, crate::transport::Variant::S2, crate::transport::Variant::D] {
            let c1: [Vec<M31>; 26] = core::array::from_fn(|_| (0..1024).map(|_| rng.m31()).collect());
            let h1: [QM31; 1024] = core::array::from_fn(|_| rng.qm31());
            let g: [QM31; 1024] = core::array::from_fn(|_| rng.qm31());
            let d: [QM31; 1024] = core::array::from_fn(|_| rng.qm31());
            let columns = semantic_columns(&c1, &h1, &g, &d);
            let pinned: [Vec<QM31>; 29] = core::array::from_fn(|lane| match lane {
                0..=25 => c1[lane].iter().copied().map(lift).collect(),
                26 => h1.to_vec(),
                27 => g.to_vec(),
                _ => d.to_vec(),
            });
            assert_eq!(columns, pinned);
            let dc = variant.coefficients(&d);
            let mut mask_sum = rows_mask_sum(&columns);
            mask_sum = mask_sum.add(side_fold(&dc, 0).mul_m31(M31(512)));
            mask_sum = mask_sum.add(side_fold(&dc, 1).mul_m31(M31(512)));
            assert_eq!(mask_sum, orig::mask_sum_orig(&columns, &dc));
            // first commitment columns: same variant and same referent per index
            let first = first_columns(&c1, &d);
            let base: [&[M31; 1024]; 26] = core::array::from_fn(|i| c1[i].as_slice().try_into().unwrap());
            for (i, column) in first.iter().enumerate() {
                match (i < 26, column) {
                    (true, Column::Base(b)) => assert!(core::ptr::eq(*b, base[i])),
                    (false, Column::Extension(e)) => assert!(core::ptr::eq(*e, &d)),
                    _ => panic!("column {i} has the wrong kind"),
                }
            }
            // row 25 and row 26 payloads
            let alpha: [QM31; 10] = core::array::from_fn(|_| rng.qm31());
            let claims = point_claims(&columns, &alpha).unwrap();
            let extras = column_extras(&columns, variant, alpha[8], alpha[9]);
            let pinned_extras: [QM31; 29] = core::array::from_fn(|l| {
                let rows: &[QM31; 1024] = columns[l].as_slice().try_into().unwrap();
                extra(&variant.coefficients(rows), alpha[8], alpha[9])
            });
            assert_eq!(extras, pinned_extras);
            assert_eq!(
                wire::encode_values(before_z0_values(&claims, &extras)),
                wire::encode_values(claims.into_iter().flatten().chain(pinned_extras).map(WideExact::from_qm31)),
            );
            let z = Point { x: rng.qm31(), y: rng.qm31() };
            let pinned_endpoint = columns.iter().map(|col| {
                let message: &[QM31; 1024] = col.as_slice().try_into().unwrap();
                let coefficients = variant.coefficients(message);
                let message = &coefficients;
                WideExact::from_qm31(eval_message(message, Point { x: z.x, y: z.y }))
            });
            assert_eq!(
                wire::encode_values(endpoint_values(&columns, variant, Point { x: z.x, y: z.y })),
                wire::encode_values(pinned_endpoint),
            );
        }
    }

    #[test]
    fn noncanonical_inputs_matches_pinned() {
        let mut rng = Rng(0x0bad_cafe_dead_beef);
        let c1: [Vec<M31>; 26] = core::array::from_fn(|_| (0..1024).map(|_| rng.m31()).collect());
        let d: [QM31; 1024] = core::array::from_fn(|_| rng.qm31());
        let g: [QM31; 1024] = core::array::from_fn(|_| rng.qm31());
        let check = |c1: &[Vec<M31>; 26], d: &[QM31; 1024], g: &[QM31; 1024]| {
            let got = noncanonical_inputs(c1, d, g);
            assert_eq!(got, orig::noncanonical_orig(c1, d, g));
            got
        };
        assert!(!check(&c1, &d, &g));
        for bad in [P, P + 1, u32::MAX] {
            let mut c = c1.clone();
            c[(bad % 26) as usize][(bad % 1024) as usize] = M31(bad);
            assert!(check(&c, &d, &g));
        }
        let mut c = c1.clone();
        c[25].push(M31::ZERO);
        assert!(check(&c, &d, &g));
        let mut c = c1.clone();
        c[3].pop();
        assert!(check(&c, &d, &g));
        for which in 0..2 {
            for part in 0..4 {
                let (mut dd, mut gg) = (d, g);
                let target = if which == 0 { &mut dd[517] } else { &mut gg[3] };
                match part {
                    0 => target.c0.a = M31(P),
                    1 => target.c0.b = M31(P + 5),
                    2 => target.c1.a = M31(u32::MAX),
                    _ => target.c1.b = M31(P),
                }
                assert!(check(&c1, &dd, &gg));
            }
        }
    }

    #[cfg(feature = "r1p-check")]
    #[test]
    fn copy_row_values_and_no_pole_match_pinned() {
        let mut rng = Rng(0x5151_7272_9393_a4a4);
        for withdrawal in [false, true] {
            let fixture = aspis_prover::r0_fixture::prepare(withdrawal);
            for _ in 0..3 {
                let lambda = rng.qm31();
                let new = lean_copy_row_values(&fixture.compiled.trace, lambda);
                assert_eq!(new, orig::lean_copy_row_values(&fixture.compiled.trace, lambda));
                let values = new.unwrap();
                let mut chis = alloc::vec![rng.qm31(), QM31::ZERO];
                // values of active and inactive rows, both sides and slots
                for row in [0usize, 1, 17, 255, 511, 1023] {
                    for side in 0..2 { for slot in 0..2 { chis.push(values[row][side][slot]); } }
                }
                for chi in chis {
                    assert_eq!(no_pole(&fixture.compiled, lambda, chi), orig::no_pole(&fixture.compiled, lambda, chi));
                }
            }
        }
    }

    /// A deterministic commitment backend for the whole-function test: the
    /// root is a SHA-256 of the column values in order.
    struct HashCommitments;
    impl Commitments for HashCommitments {
        fn c1(&mut self, columns: [Column<'_>; 27]) -> Result<[u8; 32], Error> {
            use sha2::Digest;
            let mut h = sha2::Sha256::new();
            for column in columns {
                match column {
                    Column::Base(v) => { h.update([0u8]); for x in v { h.update(x.0.to_le_bytes()); } }
                    Column::Extension(v) => { h.update([1u8]); for x in v { let mut b = [0; 16]; x.write_le_bytes(&mut b); h.update(b); } }
                }
            }
            Ok(h.finalize().into())
        }
        fn c2(&mut self, columns: [&[QM31; 1024]; 2]) -> Result<[u8; 32], Error> {
            use sha2::Digest;
            let mut h = sha2::Sha256::new();
            for v in columns { for x in v { let mut b = [0; 16]; x.write_le_bytes(&mut b); h.update(b); } }
            Ok(h.finalize().into())
        }
    }

    fn summary<H: Digest32>(r: Result<BuiltSemantics<H>, Error>) -> Result<(Vec<u8>, Challenges, [QM31; 10], [u8; 32], [u8; 32], [[u8; 32]; 2], [Vec<QM31>; 29], [aspis_core::circle::SecureCirclePoint; 2]), Error> {
        r.map(|b| { let s = b.transcript.state(); (b.bytes, b.challenges, b.alpha, b.state_before_z0, s, b.roots, b.columns, b.z) })
    }

    /// Whole build_with_helper_mode (pinned copy vs rewrite) on the r0
    /// fixture's compiled C1 plus random mask-only columns, D and G, for each
    /// transport variant, and on one noncanonical input.
    #[test]
    fn build_with_helper_mode_matches_pinned_on_fixture() {
        use aspis_core::digest::LegacyHashFn;
        use aspis_prover::HOST_HASH;
        let mut rng = Rng(0x7777_1111_3333_5555);
        let fixture = aspis_prover::r0_fixture::prepare(false);
        let public = fixture.public();
        let compiled = &fixture.compiled;
        let mut ok = 0;
        for variant in [crate::transport::Variant::S1, crate::transport::Variant::S2, crate::transport::Variant::D] {
            let mask_only: [Vec<M31>; 10] = core::array::from_fn(|_| (0..1024).map(|_| rng.m31()).collect());
            let c1: [Vec<M31>; 26] = core::array::from_fn(|i| if i < 16 { compiled.semantic_c1.c1[i].clone() } else { mask_only[i - 16].clone() });
            let d: [QM31; 1024] = core::array::from_fn(|_| rng.qm31());
            let g: [QM31; 1024] = core::array::from_fn(|_| rng.qm31());
            let pad = [QM31::ZERO; 1024];
            let helper = |lambda, chi| build_pool_v1_pair_forest_copy_helper_v1(&compiled.trace, public.transition().live_snapshot.next_pair_index, lambda, chi).map_err(|_| Error::Public);
            // Timing is informational only (one sample each, same process).
            let t = std::time::Instant::now();
            let old = summary(orig::build_with_helper_mode(public, &c1, &d, &g, &pad, helper, &mut HashCommitments, LegacyHashFn(HOST_HASH), variant));
            let t_old = t.elapsed();
            let t = std::time::Instant::now();
            let new = summary(build_with_helper_mode(public, &c1, &d, &g, &pad, helper, &mut HashCommitments, LegacyHashFn(HOST_HASH), variant));
            let t_new = t.elapsed();
            std::eprintln!("{variant:?}: pinned {t_old:?}, rewritten {t_new:?}");
            if new.is_ok() { ok += 1; }
            assert_eq!(new, old);
            let mut bad = d;
            bad[9].c1.a = M31(P);
            let new = summary(build_with_helper_mode(public, &c1, &bad, &g, &pad, helper, &mut HashCommitments, LegacyHashFn(HOST_HASH), variant));
            let old = summary(orig::build_with_helper_mode(public, &c1, &bad, &g, &pad, helper, &mut HashCommitments, LegacyHashFn(HOST_HASH), variant));
            assert_eq!(new, old);
            assert_eq!(new, Err(Error::Public));
        }
        std::eprintln!("build_with_helper_mode: {ok}/3 variants reached Ok");
    }
}
