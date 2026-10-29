import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_ReserveBuild
open Aeneas Aeneas.Std ProverRwFull PV_W_TypedEffects
open PV_W_RecursiveLaws
variable [ExternalTypes]

def program
  {T0 : Type} (state_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (self : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (nonce_store : T0) :
  P ((core.result.Result
    (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
    aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × T0) := do
  let b ← invoke "core.array.equality.PartialEqArray.ne" (fun ops =>
      letI : ExternalFuns := ops
      core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      context.mask_nonce self.mask_nonce)
  if b then
    pure (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
      nonce_store)
  else
    let i ← invoke "aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)
    if context.mask_layout_fingerprint != i then
      pure (core.result.Result.Err
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
        nonce_store)
    else
      let i1 ← invoke "aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1" (fun ops =>
          letI : ExternalFuns := ops
          aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1)
      if context.layout_factor_fingerprint != i1 then
        pure (core.result.Result.Err
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
          nonce_store)
      else
        let (b1, nonce_store1) ← invoke "state_only_hidingStateOnlyMaskNonceStoreInst.\u00abreserve\u00bb" (fun ops =>
            letI : ExternalFuns := ops
            state_only_hidingStateOnlyMaskNonceStoreInst.«reserve» nonce_store
            context.statement_digest context.mask_nonce)
        if b1 then
          let a ← invoke "zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref" (fun ops =>
              letI : ExternalFuns := ops
              zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
              (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
              U8.Insts.ZeroizeDefaultIsZeroes)) self.field_mask_entropy)
          let (r, pre_reserved) ← invoke "aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref" (fun ops =>
              letI : ExternalFuns := ops
              aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref
              aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
              hash precommit_binding context a
              {
              statement_digest := context.statement_digest,
              mask_nonce := context.mask_nonce,
              consumed := false
              })
          let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
              letI : ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTry.branch r)
          match cf with
          | core.ops.control_flow.ControlFlow.Continue val =>
            if pre_reserved.consumed then
              let s ← invoke "Aeneas.Std.lift" (fun ops =>
                  letI : ExternalFuns := ops
                  Aeneas.Std.lift (Array.to_slice precommit_binding))
              let a1 ← invoke "aspis_core.state_only_hiding.StateOnlyHidingContext.encode" (fun ops =>
                  letI : ExternalFuns := ops
                  aspis_core.state_only_hiding.StateOnlyHidingContext.encode
                  context)
              let s1 ← invoke "Aeneas.Std.lift" (fun ops =>
                  letI : ExternalFuns := ops
                  Aeneas.Std.lift (Array.to_slice a1))
              let s2 ← invoke "zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref" (fun ops =>
                  letI : ExternalFuns := ops
                  zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref
                  (Array.Insts.CoreConvertAsRefSlice Std.U8 32#usize)
                  (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
                  U8.Insts.ZeroizeDefaultIsZeroes)) self.field_mask_entropy)
              let s3 ← invoke "Aeneas.Std.lift" (fun ops =>
                  letI : ExternalFuns := ops
                  Aeneas.Std.lift (Array.to_slice
                  (Array.make 4#usize [
                  aspis_prover.state_only_entropy.POOL_V1_SOURCE_SEED_DOMAIN,
                  s, s1, s2
                  ])))
              let a2 ← invoke "hash" (fun ops =>
                  letI : ExternalFuns := ops
                  hash s3)
              let source_mask_seed ← invoke "zeroize.Zeroizing.new" (fun ops =>
                  letI : ExternalFuns := ops
                  zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
                  (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a2)
              let _ ← invoke "zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize" (fun ops =>
                  letI : ExternalFuns := ops
                  zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize
                  (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
                  U8.Insts.ZeroizeDefaultIsZeroes)) self.field_mask_entropy)
              pure (core.result.Result.Ok
                ({
                mask_nonce := self.mask_nonce,
                precommit_binding,
                reserved_context := context,
                leaf_salt_seed := self.leaf_salt_seed,
                source_mask_seed
                }, val), nonce_store1)
            else
              pure (core.result.Result.Err
                aspis_prover.state_only_hiding.StateOnlyMaskBuildError.ReusedMaskNonce,
                nonce_store1)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r1 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                letI : ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets
                × aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
                (core.convert.FromSame
                aspis_prover.state_only_hiding.StateOnlyMaskBuildError)
                residual)
            pure (r1, nonce_store1)
        else
          pure (core.result.Result.Err
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError.ReusedMaskNonce,
            nonce_store1)

theorem erase_program (ops : ExternalFuns)
  {T0 : Type} (state_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (self : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (nonce_store : T0) :
  erase ops (program state_only_hidingStateOnlyMaskNonceStoreInst self hash precommit_binding context nonce_store) =
    @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1 _ ops T0 state_only_hidingStateOnlyMaskNonceStoreInst self hash precommit_binding context nonce_store := by
  unfold program aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro b
    try dsimp only
    apply PV_W_IfLaws.erase_if_congr
    ·
      rfl
    ·
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro i
        try dsimp only
        apply PV_W_IfLaws.erase_if_congr
        ·
          rfl
        ·
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro i1
            try dsimp only
            apply PV_W_IfLaws.erase_if_congr
            ·
              rfl
            ·
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · rintro ⟨b1, nonce_store1⟩
                try dsimp only
                apply PV_W_IfLaws.erase_if_congr
                ·
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro a
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · rintro ⟨r, pre_reserved⟩
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact erase_invoke ops _ _
                      · intro cf
                        try dsimp only
                        cases cf with
                        | Continue val =>
                          try dsimp only
                          apply PV_W_IfLaws.erase_if_congr
                          ·
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              exact erase_invoke ops _ _
                            · intro s
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact erase_invoke ops _ _
                              · intro a1
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro s1
                                  try dsimp only
                                  rw [erase_bind]
                                  apply PV_W_RecursiveLaws.bind_congr
                                  ·
                                    exact erase_invoke ops _ _
                                  · intro s2
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact erase_invoke ops _ _
                                    · intro s3
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
                                      · intro a2
                                        try dsimp only
                                        rw [erase_bind]
                                        apply PV_W_RecursiveLaws.bind_congr
                                        ·
                                          exact erase_invoke ops _ _
                                        · intro source_mask_seed
                                          try dsimp only
                                          rw [erase_bind]
                                          apply PV_W_RecursiveLaws.bind_congr
                                          ·
                                            exact erase_invoke ops _ _
                                          · intro _
                                            rfl
                          ·
                            rfl
                        | Break residual =>
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact erase_invoke ops _ _
                          · intro r1
                            rfl
                ·
                  rfl

#print axioms erase_program
end R1Z.PV_W_ReserveBuild
