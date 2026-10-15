fn withdrawal_common(public: &PoolV1WithdrawalPublicV1) -> CommonPublicV1 {
    CommonPublicV1 {
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor_sequence: public.anchor_sequence,
        anchor_root: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
    }
}