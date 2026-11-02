import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OpMaterialFromEntropy
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  op112_OPEN : P (Std.U64)
  op113_OPEN : P (Std.U64)
  op132_OPEN : P ((core.result.Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell) aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1))
  op12_OPEN : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
      core.ops.function.FnOnce O E F) (arg0 : (core.result.Result T E)) (arg1 : O), P ((core.result.Result T F))
  pool_v1_pair_forest_copy_active_rows_OPEN : P ((core.result.Result (Array Bool 1024#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError))
  build_mask_material_for_layout_OPEN : ∀ {T0 : Type} (StateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (private_entropy : Array Std.U8 32#usize) (nonce_store : T0)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize), P (((core.result.Result
    aspis_prover.state_only_hiding.StateOnlyMaskMaterial
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × T0))

structure Compatible (c : Callees) : Prop where
  op112_fixed : FinishedView (c.op112_OPEN) (aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)
  op113_fixed : FinishedView (c.op113_OPEN) (aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1)
  op132_fixed : FinishedView (c.op132_OPEN) (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1)
  op12_fixed : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
      core.ops.function.FnOnce O E F) (arg0 : (core.result.Result T E)) (arg1 : O), FinishedView (c.op12_OPEN opsfunctionFnOnceOTupleEFInst arg0 arg1) (core.result.Result.map_err opsfunctionFnOnceOTupleEFInst arg0 arg1)
  pool_v1_pair_forest_copy_active_rows_fixed : FinishedView (c.pool_v1_pair_forest_copy_active_rows_OPEN) (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows)
  build_mask_material_for_layout_fixed : ∀ {T0 : Type} (StateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (private_entropy : Array Std.U8 32#usize) (nonce_store : T0)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize), FinishedView (c.build_mask_material_for_layout_OPEN StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store cells active) (aspis_prover.state_only_hiding.build_mask_material_for_layout StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store cells active)

def run
  {T0 : Type} (StateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (private_entropy : Array Std.U8 32#usize) (nonce_store : T0) (c : Callees) : P ((core.result.Result
    aspis_prover.state_only_hiding.StateOnlyMaskMaterial
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × T0) := do
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
      let r ← c.op132_OPEN
      let r1 ← c.op12_OPEN
          (aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1StateOnlyMaskBuildError
          StateOnlyMaskNonceStoreInst) r ()
      let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let s := alloc.vec.Vec.deref val
        let r2 ← c.pool_v1_pair_forest_copy_active_rows_OPEN
        let cf1 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          c.build_mask_material_for_layout_OPEN
            StateOnlyMaskNonceStoreInst hash precommit_binding context
            private_entropy nonce_store s val1
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              aspis_prover.state_only_hiding.StateOnlyMaskMaterial
              (core.convert.FromSame
              aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual)
          pure (r3, nonce_store)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            aspis_prover.state_only_hiding.StateOnlyMaskMaterial
            (core.convert.FromSame
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual)
        pure (r2, nonce_store)

theorem run_fixed
  {T0 : Type} (StateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (private_entropy : Array Std.U8 32#usize) (nonce_store : T0) (c : Callees) (compatible : Compatible c) :
    FinishedView (run StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store c) (aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store) := by
  unfold run aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref
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
            exact compatible.op132_fixed
          · intro r
            try dsimp only
            apply PV_EVH_Prefix.bind_fixed
            ·
              exact compatible.op12_fixed _ _ _
            · intro r1
              try dsimp only
              apply PV_EVH_Prefix.bind_fixed
              ·
                exact PV_EVH_Prefix.lift_fixed _
              · intro cf
                try dsimp only
                cases cf with
                | Continue val =>
                  let s := alloc.vec.Vec.deref val
                  try dsimp only
                  try dsimp only
                  apply PV_EVH_Prefix.bind_fixed
                  ·
                    exact compatible.pool_v1_pair_forest_copy_active_rows_fixed
                  · intro r2
                    try dsimp only
                    apply PV_EVH_Prefix.bind_fixed
                    ·
                      exact PV_EVH_Prefix.lift_fixed _
                    · intro cf1
                      try dsimp only
                      cases cf1 with
                      | Continue val1 =>
                        exact compatible.build_mask_material_for_layout_fixed _ _ _ _ _ _ _ _
                      | Break residual =>
                        try dsimp only
                        apply PV_EVH_Prefix.bind_fixed
                        ·
                          exact PV_EVH_Prefix.lift_fixed _
                        · intro r3
                          exact PV_EVH_Prefix.lift_fixed _
                | Break residual =>
                  try dsimp only
                  apply PV_EVH_Prefix.bind_fixed
                  ·
                    exact PV_EVH_Prefix.lift_fixed _
                  · intro r2
                    exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_OpMaterialFromEntropy
