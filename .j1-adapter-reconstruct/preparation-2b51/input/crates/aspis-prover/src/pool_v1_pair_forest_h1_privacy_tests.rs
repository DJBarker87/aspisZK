// Research-only source regression. Included inside
// `pool_v1_pair_forest_honest::tests` to reuse the genuine compiler fixture.

#[test]
fn v8_h1_incidence_and_duplicate_selection_delta() {
    use aspis_core::field::{CM31, M31, QM31};
    use aspis_statement::logup::compress_tagged_tuple;
    use aspis_statement::pool_v1::{
        pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1,
        pair_forest_trace::{build_pool_v1_pair_forest_copy_registry_v1, PoolV1PairForestTraceV1},
        pair_trace::{
            PoolV1PairCopyTupleV1, PoolV1PairCopyWeightV1, PoolV1PairTraceBankV1,
            PoolV1PairTraceVariantV1, PoolV1PairTupleLimbV1,
        },
        pool_v1_nullifier, PoolV1PairLeafWitnessV1,
    };

    fn tuple_values(trace: &PoolV1PairForestTraceV1, tuple: PoolV1PairCopyTupleV1) -> [M31; 16] {
        tuple.limbs.map(|limb| match limb {
            PoolV1PairTupleLimbV1::Zero => M31::ZERO,
            PoolV1PairTupleLimbV1::Cell { source, offset } => {
                let columns = match source.bank {
                    PoolV1PairTraceBankV1::Stable => &trace.stable.c1,
                    PoolV1PairTraceBankV1::Late => &trace.late,
                };
                columns[source.cell.column as usize][source.cell.row as usize].add(offset)
            }
        })
    }

    fn public_weight(
        weight: PoolV1PairCopyWeightV1,
        append: u64,
        variant: PoolV1PairTraceVariantV1,
    ) -> M31 {
        match weight {
            PoolV1PairCopyWeightV1::One => M31::ONE,
            PoolV1PairCopyWeightV1::PrivateTransferOnly => M31(u32::from(
                variant == PoolV1PairTraceVariantV1::PrivateTransfer,
            )),
            PoolV1PairCopyWeightV1::WithdrawalOnly => {
                M31(u32::from(variant == PoolV1PairTraceVariantV1::Withdrawal))
            }
            PoolV1PairCopyWeightV1::AppendCurrentLeft { level } => {
                M31(1 - ((append >> level) & 1) as u32)
            }
            PoolV1PairCopyWeightV1::AppendCurrentRight { level } => {
                M31(((append >> level) & 1) as u32)
            }
        }
    }

    fn check_incidence(
        trace: &PoolV1PairForestTraceV1,
        append: u64,
        lambda: QM31,
        chi: QM31,
    ) -> Vec<QM31> {
        let registry = build_pool_v1_pair_forest_copy_registry_v1().unwrap();
        assert_eq!(registry.len(), 136);
        assert_eq!(registry[19].tag, M31(0x4300_0013));
        assert_eq!(
            (registry[19].producer.row, registry[19].consumer.row),
            (913, 1017)
        );
        let mut expected = vec![QM31::ZERO; 1024];
        for link in registry {
            let weight = public_weight(link.weight, append, trace.variant);
            if weight == M31::ZERO {
                continue;
            }
            let producer = tuple_values(trace, link.producer);
            let consumer = tuple_values(trace, link.consumer);
            assert_eq!(
                producer, consumer,
                "honest checked source violates active copy link {}",
                link.id
            );
            let compressed = compress_tagged_tuple(link.tag, &producer, lambda);
            let coefficient = chi
                .sub(compressed)
                .try_inv()
                .expect("diagnostic active pole")
                .mul_m31(weight);
            let producer_row = link.producer.row as usize;
            let consumer_row = link.consumer.row as usize;
            expected[producer_row] = expected[producer_row].add(coefficient);
            expected[consumer_row] = expected[consumer_row].sub(coefficient);
        }
        let actual = build_pool_v1_pair_forest_copy_helper_v1(trace, append, lambda, chi).unwrap();
        assert_eq!(actual, expected, "literal helper differs from D*a");
        assert_eq!(
            actual.iter().copied().fold(QM31::ZERO, QM31::add),
            QM31::ZERO
        );
        actual
    }

    let mut first = transfer_fixture();
    assert!(!first.witness.input.pair.selected_second);
    let commitment = first.witness.input.pair.pair_leaf.first_commitment;
    first.witness.input.pair.pair_leaf =
        PoolV1PairLeafWitnessV1::two_outputs(commitment, commitment).unwrap();
    first.public.anchor_root = global_anchor(&first.witness.input);
    first.public.nullifier = pool_v1_nullifier(
        &first.witness.input.pair.nullifier_key,
        &first.witness.input.pair.salt,
    );
    let mut second = first;
    second.witness.input.pair.selected_second = true;
    assert_eq!(first.public, second.public);
    assert_eq!(first.snapshot, second.snapshot);
    let checked_zero = run_transfer(&first).unwrap();
    let checked_one = run_transfer(&second).unwrap();
    assert_eq!(
        checked_zero.compilation.public_statement,
        checked_one.compilation.public_statement
    );

    // Common diagnostic challenges only. They are not a protocol-domain change.
    let lambda = QM31::from_cm31(CM31 {
        a: M31(7),
        b: M31(3),
    });
    let chi = QM31 {
        c0: CM31 {
            a: M31(17),
            b: M31(19),
        },
        c1: CM31 {
            a: M31(23),
            b: M31(29),
        },
    };
    let append = first.snapshot.next_pair_index;
    let h_zero = check_incidence(&checked_zero.compilation.trace, append, lambda, chi);
    let h_one = check_incidence(&checked_one.compilation.trace, append, lambda, chi);
    let tag = QM31::from_cm31(CM31::from_m31(M31(0x4300_0013)));
    let delta = chi
        .sub(tag)
        .sub(lambda)
        .try_inv()
        .unwrap()
        .sub(chi.sub(tag).try_inv().unwrap());
    assert_ne!(delta, QM31::ZERO);
    for row in 0..1024 {
        let expected = if row == 913 {
            delta
        } else if row == 1017 {
            QM31::ZERO.sub(delta)
        } else {
            QM31::ZERO
        };
        assert_eq!(
            h_one[row].sub(h_zero[row]),
            expected,
            "unexpected H1 delta at row {row}"
        );
    }

    // Exact lambda=0 control, not a proposed challenge restriction.
    let zero_zero = check_incidence(&checked_zero.compilation.trace, append, QM31::ZERO, chi);
    let zero_one = check_incidence(&checked_one.compilation.trace, append, QM31::ZERO, chi);
    assert_eq!(zero_zero, zero_one);
}
