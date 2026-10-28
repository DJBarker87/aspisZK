import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_MaskMaterial
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  {T0 : Type} (StateOnlyMaskNonceStoreInst : Store T0)
  (hash : Hash)
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (private_entropy : Array Std.U8 32#usize) (nonce_store : T0) :
  P ((core.result.Result
    aspis_prover.state_only_hiding.StateOnlyMaskMaterial
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × T0) := do
  let i ← invoke "aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      let StateOnlyMaskNonceStoreInst := sourceStore ops StateOnlyMaskNonceStoreInst
      aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)
  if context.mask_layout_fingerprint != i then
    pure (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
      nonce_store)
  else
    let i1 ← invoke "aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        let StateOnlyMaskNonceStoreInst := sourceStore ops StateOnlyMaskNonceStoreInst
        aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1)
    if context.layout_factor_fingerprint != i1 then
      pure (core.result.Result.Err
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
        nonce_store)
    else
      let r ← invoke "aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          let StateOnlyMaskNonceStoreInst := sourceStore ops StateOnlyMaskNonceStoreInst
          aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1)
      let r1 ← invoke "core.result.Result.map_err" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          let StateOnlyMaskNonceStoreInst := sourceStore ops StateOnlyMaskNonceStoreInst
          core.result.Result.map_err
          (aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1StateOnlyMaskBuildError
          StateOnlyMaskNonceStoreInst) r ())
      let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          let StateOnlyMaskNonceStoreInst := sourceStore ops StateOnlyMaskNonceStoreInst
          core.result.Result.Insts.CoreOpsTry.branch r1)
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let s := alloc.vec.Vec.deref val
        let r2 ← invoke "aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            let StateOnlyMaskNonceStoreInst := sourceStore ops StateOnlyMaskNonceStoreInst
            aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows)
        let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            let StateOnlyMaskNonceStoreInst := sourceStore ops StateOnlyMaskNonceStoreInst
            core.result.Result.Insts.CoreOpsTry.branch r2)
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          invoke "aspis_prover.state_only_hiding.build_mask_material_for_layout" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            let StateOnlyMaskNonceStoreInst := sourceStore ops StateOnlyMaskNonceStoreInst
            aspis_prover.state_only_hiding.build_mask_material_for_layout
            StateOnlyMaskNonceStoreInst hash precommit_binding context
            private_entropy nonce_store s val1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
              letI : ExternalFuns := ops
              let hash := sourceHash ops hash
              let StateOnlyMaskNonceStoreInst := sourceStore ops StateOnlyMaskNonceStoreInst
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              aspis_prover.state_only_hiding.StateOnlyMaskMaterial
              (core.convert.FromSame
              aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual)
          pure (r3, nonce_store)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            let StateOnlyMaskNonceStoreInst := sourceStore ops StateOnlyMaskNonceStoreInst
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            aspis_prover.state_only_hiding.StateOnlyMaskMaterial
            (core.convert.FromSame
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual)
        pure (r2, nonce_store)

theorem erase_program (ops : ExternalFuns)
  {T0 : Type} (StateOnlyMaskNonceStoreInst : Store T0)
  (hash : Hash)
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (private_entropy : Array Std.U8 32#usize) (nonce_store : T0) :
  erase ops (program StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store) =
    @aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref _ ops T0 (sourceStore ops StateOnlyMaskNonceStoreInst) (sourceHash ops hash) precommit_binding context private_entropy nonce_store := by
  unfold program aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro i
    try dsimp only
    apply PV_W_Callbacks.erase_if_congr
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
        apply PV_W_Callbacks.erase_if_congr
        ·
          rfl
        ·
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro r
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro r1
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
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro r2
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro cf1
                      try dsimp only
                      cases cf1 with
                      | Continue val1 =>
                        exact erase_invoke ops _ _
                      | Break residual =>
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro r3
                          rfl
                | Break residual =>
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro r2
                    rfl

#print axioms erase_program
end R1Z.PV_W_R_MaskMaterial
