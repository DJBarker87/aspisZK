#[derive(Clone, Copy)]
struct SemanticPublic<'a> {
    variant: CompiledVariant,
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    anchor: Digest,
    nullifier: Digest,
    asset_id: M31,
    recipient: Option<Digest>,
    change: Digest,
    withdrawal_amount: Option<u32>,
    transition: &'a PoolV1PairLatePublicStatementV1,
}