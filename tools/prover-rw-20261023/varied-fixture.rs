//! Test-only honest statements; r0_fixture shape with varied pool, values and salts.
use aspis_core::field::M31;
use aspis_prover::r0_fixture::Fixture;
use aspis_statement::pool_v1::*;
pub fn prepare(withdrawal:bool,coin:u64)->Fixture {
    let pool=aspis_prover::HOST_HASH(&[b"PROVER-RW:statement",&coin.to_le_bytes()]);
    let mut empty = [[M31::ZERO; 8]; 21];
    empty[0] = pool_v1_tree_parent(&[M31::ZERO; 8], &[M31::ZERO; 8]);
    for i in 0..20 {
        empty[i + 1] = pool_v1_tree_parent(&empty[i], &empty[i]);
    }
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool,
        deployment_domain: [5; 32],
        sequence: 0,
        next_pair_index: 0,
        current_root: empty[20],
        frontier: core::array::from_fn(|i| empty[i]),
    };
    let f = aspis_prover::v7_pair_forest_fixture::prepare_v7_pair_forest_transfer_fixture_v1(
        pool, [2; 32], [3; 32], 0, [5; 32], snapshot,
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
        let mut public=f.public;
        let mut witness=f.witness;
        witness.recipient.value=100+(coin%801) as u32;
        witness.change.value=1000-witness.recipient.value;
        witness.recipient.salt=core::array::from_fn(|i|M31(401+(coin%1000000) as u32+17*i as u32));
        witness.change.salt=core::array::from_fn(|i|M31(601+(coin%1000000) as u32+17*i as u32));
        public.recipient_commitment=pool_v1_note_commitment(&witness.recipient.owner_key,witness.recipient.value,public.asset_id,&witness.recipient.salt);
        public.change_commitment=pool_v1_note_commitment(&witness.change.owner_key,witness.change.value,public.asset_id,&witness.change.salt);
        let compiled=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&public,&witness,context,snapshot).unwrap();
        let mut common=*f.statement.common();common.lane_transition=compiled.public_statement;
        return Fixture{statement:PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public},compiled};
    }
    let change = PoolV1OutputNoteWitnessV1 {
        owner_key: core::array::from_fn(|i| M31(701 + 17 * i as u32)),
        salt: core::array::from_fn(|i| M31(801 + (coin%1000000) as u32 + 17 * i as u32)),
        value: 1000-(100+(coin%801) as u32),
    };
    let public = PoolV1WithdrawalPublicV1 {
        pool: f.public.pool,
        deployment_domain: f.public.deployment_domain,
        anchor_sequence: f.public.anchor_sequence,
        anchor_root: f.public.anchor_root,
        nullifier: f.public.nullifier,
        asset_id: f.public.asset_id,
        amount: 100+(coin%801) as u32,
        destination_token_account: aspis_prover::HOST_HASH(&[b"PROVER-RW:destination",&coin.to_le_bytes()]),
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
