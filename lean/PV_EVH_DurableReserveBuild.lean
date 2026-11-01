import PV_EVH_NonceSource
import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_DurableReserveBuild
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  arrayNe_OPEN : ∀ {T : Type} {N : Usize} (inst : core.cmp.PartialEq T T) (a b : Array T N), P (Bool)
  op112_OPEN : P (Std.U64)
  op113_OPEN : P (Std.U64)
  op127_OPEN : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), P (Z)
  build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref_OPEN : ∀ {T0 : Type} (StateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (private_entropy : Array Std.U8 32#usize) (nonce_store : T0), P (((core.result.Result
    aspis_prover.state_only_hiding.StateOnlyMaskMaterial
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × T0))
  op116_OPEN : ∀ (arg0 : aspis_core.state_only_hiding.StateOnlyHidingContext), P ((Array Std.U8 81#usize))
  op131_OPEN : ∀ {T : Type} {Z : Type} (coreconvertAsRefInst : core.convert.AsRef Z T)
      (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), P (T)
  hash_OPEN : ∀ (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (s : Slice (Slice U8)), P ((Array U8 32#usize))
  op128_OPEN : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : Z), P ((zeroize.Zeroizing Z))
  op130_OPEN : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), P ((zeroize.Zeroizing Z))

structure Compatible (c : Callees) : Prop where
  arrayNe_fixed : ∀ {T : Type} {N : Usize} (inst : core.cmp.PartialEq T T) (a b : Array T N), FinishedView (c.arrayNe_OPEN inst a b) (core.array.equality.PartialEqArray.ne inst a b)
  op112_fixed : FinishedView (c.op112_OPEN) (aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)
  op113_fixed : FinishedView (c.op113_OPEN) (aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1)
  op127_fixed : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), FinishedView (c.op127_OPEN ZeroizeInst arg0) (zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref ZeroizeInst arg0)
  build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref_fixed : ∀ {T0 : Type} (StateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (private_entropy : Array Std.U8 32#usize) (nonce_store : T0), FinishedView (c.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref_OPEN StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store) (aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store)
  op116_fixed : ∀ (arg0 : aspis_core.state_only_hiding.StateOnlyHidingContext), FinishedView (c.op116_OPEN arg0) (aspis_core.state_only_hiding.StateOnlyHidingContext.encode arg0)
  op131_fixed : ∀ {T : Type} {Z : Type} (coreconvertAsRefInst : core.convert.AsRef Z T)
      (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), FinishedView (c.op131_OPEN coreconvertAsRefInst ZeroizeInst arg0) (zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref coreconvertAsRefInst ZeroizeInst arg0)
  hash_fixed : ∀ (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (s : Slice (Slice U8)), FinishedView (c.hash_OPEN hash s) (hash s)
  op128_fixed : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : Z), FinishedView (c.op128_OPEN ZeroizeInst arg0) (zeroize.Zeroizing.new ZeroizeInst arg0)
  op130_fixed : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), FinishedView (c.op130_OPEN ZeroizeInst arg0) (zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize ZeroizeInst arg0)

def run
  (self : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (nonce_store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (fileAnswers : PV_EVH_NonceWorld.Answers) (c : Callees) : P ((core.result.Result
    (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
    aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let b ← c.arrayNe_OPEN core.cmp.PartialEqU8
      context.mask_nonce self.mask_nonce
  if b then
    pure (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
      nonce_store)
  else
    let i ← c.op112_OPEN
    if context.mask_layout_fingerprint != i then
      pure (core.result.Result.Err
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
        nonce_store)
    else
      let i1 ← c.op113_OPEN
      if context.layout_factor_fingerprint != i1 then
        pure (core.result.Result.Err
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
          nonce_store)
      else
        let (b1, nonce_store1) ← PV_EVH_Prefix.ofM (PV_EVH_NonceSource.reserve fileAnswers nonce_store context.statement_digest context.mask_nonce)
        if b1 then
          let a ← c.op127_OPEN
              (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
              U8.Insts.ZeroizeDefaultIsZeroes)) self.field_mask_entropy
          let (r, pre_reserved) ← c.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref_OPEN
              aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
              hash precommit_binding context a
              {
              statement_digest := context.statement_digest,
              mask_nonce := context.mask_nonce,
              consumed := false
              }
          let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r)
          match cf with
          | core.ops.control_flow.ControlFlow.Continue val =>
            if pre_reserved.consumed then
              let s ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice precommit_binding))
              let a1 ← c.op116_OPEN
                  context
              let s1 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice a1))
              let s2 ← c.op131_OPEN
                  (Array.Insts.CoreConvertAsRefSlice Std.U8 32#usize)
                  (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
                  U8.Insts.ZeroizeDefaultIsZeroes)) self.field_mask_entropy
              let s3 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice
                  (Array.make 4#usize [
                  aspis_prover.state_only_entropy.POOL_V1_SOURCE_SEED_DOMAIN,
                  s, s1, s2
                  ])))
              let a2 ← c.hash_OPEN hash s3
              let source_mask_seed ← c.op128_OPEN (Array.Insts.ZeroizeZeroize 32#usize
                  (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a2
              let _ ← c.op130_OPEN
                  (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
                  U8.Insts.ZeroizeDefaultIsZeroes)) self.field_mask_entropy
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
            let r1 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
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

theorem run_fixed
  (self : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (nonce_store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (fileAnswers : PV_EVH_NonceWorld.Answers) (c : Callees) (compatible : Compatible c) (files_same : PV_EVH_NonceWorld.Compatible fileAnswers) :
    FinishedView (run self hash precommit_binding context nonce_store fileAnswers c) (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1 aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore self hash precommit_binding context nonce_store) := by
  unfold run aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact compatible.arrayNe_fixed _ _ _
  · intro b
    by_cases condition : b
    · simp only [condition,if_true]
      exact PV_EVH_Prefix.lift_fixed _
    · simp only [condition,if_false]
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact compatible.op112_fixed
      · intro i
        by_cases condition : context.mask_layout_fingerprint != i
        · simp only [condition,if_true]
          exact PV_EVH_Prefix.lift_fixed _
        · simp only [condition,if_false]
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact compatible.op113_fixed
          · intro i1
            by_cases condition : context.layout_factor_fingerprint != i1
            · simp only [condition,if_true]
              exact PV_EVH_Prefix.lift_fixed _
            · simp only [condition,if_false]
              try dsimp only
              apply PV_EVH_Prefix.bind_fixed
              ·
                exact PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_NonceSource.reserve_fixed fileAnswers files_same _ _ _)
              · rintro ⟨b1, nonce_store1⟩
                by_cases condition : b1
                · simp only [condition,if_true]
                  try dsimp only
                  apply PV_EVH_Prefix.bind_fixed
                  ·
                    exact compatible.op127_fixed _ _
                  · intro a
                    try dsimp only
                    apply PV_EVH_Prefix.bind_fixed
                    ·
                      exact compatible.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref_fixed _ _ _ _ _ _
                    · rintro ⟨r, pre_reserved⟩
                      try dsimp only
                      apply PV_EVH_Prefix.bind_fixed
                      ·
                        exact PV_EVH_Prefix.lift_fixed _
                      · intro cf
                        try dsimp only
                        cases cf with
                        | Continue val =>
                          by_cases condition : pre_reserved.consumed
                          · simp only [condition,if_true]
                            try dsimp only
                            apply PV_EVH_Prefix.bind_fixed
                            ·
                              exact PV_EVH_Prefix.lift_fixed _
                            · intro s
                              try dsimp only
                              apply PV_EVH_Prefix.bind_fixed
                              ·
                                exact compatible.op116_fixed _
                              · intro a1
                                try dsimp only
                                apply PV_EVH_Prefix.bind_fixed
                                ·
                                  exact PV_EVH_Prefix.lift_fixed _
                                · intro s1
                                  try dsimp only
                                  apply PV_EVH_Prefix.bind_fixed
                                  ·
                                    exact compatible.op131_fixed _ _ _
                                  · intro s2
                                    try dsimp only
                                    apply PV_EVH_Prefix.bind_fixed
                                    ·
                                      exact PV_EVH_Prefix.lift_fixed _
                                    · intro s3
                                      try dsimp only
                                      apply PV_EVH_Prefix.bind_fixed
                                      ·
                                        exact compatible.hash_fixed _ _
                                      · intro a2
                                        try dsimp only
                                        apply PV_EVH_Prefix.bind_fixed
                                        ·
                                          exact compatible.op128_fixed _ _
                                        · intro source_mask_seed
                                          try dsimp only
                                          apply PV_EVH_Prefix.bind_fixed
                                          ·
                                            exact compatible.op130_fixed _ _
                                          · intro _
                                            exact PV_EVH_Prefix.lift_fixed _
                          · simp only [condition,if_false]
                            exact PV_EVH_Prefix.lift_fixed _
                        | Break residual =>
                          try dsimp only
                          apply PV_EVH_Prefix.bind_fixed
                          ·
                            exact PV_EVH_Prefix.lift_fixed _
                          · intro r1
                            exact PV_EVH_Prefix.lift_fixed _
                · simp only [condition,if_false]
                  exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_DurableReserveBuild
