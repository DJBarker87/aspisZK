//! Deterministic, explicitly insecure R0 fixtures for both builder variants.
use aspis_core::field::{CM31, M31, QM31};
use aspis_statement::pool_v1::{
    pair_forest_semantic_terminal::r0::Public,
    pair_forest_trace::PoolV1PairForestMergedC1CompilationV1, *,
};

pub struct Fixture {
    pub statement: PoolV1PairForestTerminalStatementV1,
    pub compiled: PoolV1PairForestMergedC1CompilationV1,
}
impl Fixture {
    pub fn public(&self) -> Public<'_> {
        statement_public(&self.statement)
    }
    pub fn prove(&self) -> Result<Vec<u8>, aspis_statement::r0::Error> {
        let masks = core::array::from_fn(|lane| {
            (0..1024)
                .map(|r| M31(((lane + 16) * 103 + r * 7 + 19) as u32))
                .collect()
        });
        let d = core::array::from_fn(|row| QM31 {
            c0: CM31::new(M31(row as u32 + 3), M31(11)),
            c1: CM31::new(M31(17), M31(19)),
        });
        let g = core::array::from_fn(|row| QM31::from_cm31(CM31::from_m31(M31(row as u32 + 5))));
        crate::r0::r0_prove(
            self.public(),
            &self.compiled,
            &masks,
            &d,
            &g,
            crate::HOST_HASH,
        )
    }
}
pub fn statement_public(statement: &PoolV1PairForestTerminalStatementV1) -> Public<'_> {
    match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { common, public } => {
            Public::Transfer(public, &common.lane_transition)
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { common, public } => {
            Public::Withdrawal(public, &common.lane_transition)
        }
    }
}
pub fn prepare(withdrawal: bool) -> Fixture {
    let mut empty = [[M31::ZERO; 8]; 21];
    empty[0] = pool_v1_tree_parent(&[M31::ZERO; 8], &[M31::ZERO; 8]);
    for i in 0..20 {
        empty[i + 1] = pool_v1_tree_parent(&empty[i], &empty[i]);
    }
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: [1; 32],
        deployment_domain: [5; 32],
        sequence: 0,
        next_pair_index: 0,
        current_root: empty[20],
        frontier: core::array::from_fn(|i| empty[i]),
    };
    let f = crate::v7_pair_forest_fixture::prepare_v7_pair_forest_transfer_fixture_v1(
        [1; 32], [2; 32], [3; 32], 0, [5; 32], snapshot,
    )
    .unwrap();
    let context = PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            pool: f.public.pool,
            deployment_domain: f.public.deployment_domain,
            anchor_sequence: f.public.anchor_sequence,
            anchor_root: f.public.anchor_root,
            asset_id: f.public.asset_id,
        },
        spent_nullifiers: &[],
    };
    if !withdrawal {
        let compiled = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
            &f.public, &f.witness, context, snapshot,
        )
        .unwrap();
        return Fixture {
            statement: f.statement,
            compiled,
        };
    }
    let change = PoolV1OutputNoteWitnessV1 {
        owner_key: core::array::from_fn(|i| M31(701 + 17 * i as u32)),
        salt: core::array::from_fn(|i| M31(801 + 17 * i as u32)),
        value: 750,
    };
    let public = PoolV1WithdrawalPublicV1 {
        pool: f.public.pool,
        deployment_domain: f.public.deployment_domain,
        anchor_sequence: f.public.anchor_sequence,
        anchor_root: f.public.anchor_root,
        nullifier: f.public.nullifier,
        asset_id: f.public.asset_id,
        amount: 250,
        destination_token_account: [6; 32],
        change_commitment: pool_v1_note_commitment(
            &change.owner_key,
            change.value,
            f.public.asset_id,
            &change.salt,
        ),
    };
    let witness = PoolV1PairForestWithdrawalWitnessV1 {
        input: f.witness.input,
        change,
    };
    let compiled =
        compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(&public, &witness, context, snapshot)
            .unwrap();
    let mut common = *f.statement.common();
    common.lane_transition = compiled.public_statement;
    Fixture {
        statement: PoolV1PairForestTerminalStatementV1::Withdrawal { common, public },
        compiled,
    }
}
