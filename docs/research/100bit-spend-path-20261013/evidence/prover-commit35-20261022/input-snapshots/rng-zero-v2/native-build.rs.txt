impl StateOnlyAttemptSecrets {
pub fn reserve_and_build_pool_v1_pair_forest_mask_material_v1(
        mut self,
        hash: HashFn,
        precommit_binding: [u8; 32],
        context: StateOnlyHidingContext,
        nonce_store: &mut impl StateOnlyMaskNonceStore,
    ) -> Result<(ReservedStateOnlyAttemptSecrets, StateOnlyMaskMaterial), StateOnlyMaskBuildError>
    {
        if context.mask_nonce != self.mask_nonce
            || context.mask_layout_fingerprint
                != PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
            || context.layout_factor_fingerprint
                != PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
        {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        if !nonce_store.reserve(context.statement_digest, context.mask_nonce) {
            return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
        }
        let mut pre_reserved = PreReservedNonce {
            statement_digest: context.statement_digest,
            mask_nonce: context.mask_nonce,
            consumed: false,
        };
        let material = build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref(
            hash,
            precommit_binding,
            context,
            &self.field_mask_entropy,
            &mut pre_reserved,
        )?;
        if !pre_reserved.consumed {
            return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
        }
        let source_mask_seed = Zeroizing::new(hash(&[
            POOL_V1_SOURCE_SEED_DOMAIN,
            &precommit_binding,
            &context.encode(),
            self.field_mask_entropy.as_ref(),
        ]));
        self.field_mask_entropy.zeroize();
        Ok((
            ReservedStateOnlyAttemptSecrets {
                mask_nonce: self.mask_nonce,
                precommit_binding,
                reserved_context: context,
                leaf_salt_seed: self.leaf_salt_seed,
                source_mask_seed,
            },
            material,
        ))
    }
}
