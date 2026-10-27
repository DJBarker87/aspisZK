import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix006
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref`.
Recursive calls remain the original extracted calls. -/
def continueAfter {T0 : Type} (StateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (precommit_binding : Array Std.U8 32#usize) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (private_entropy : Array Std.U8 32#usize) (nonce_store : T0) (out : Payload (aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)) : Result ((core.result.Result
    aspis_prover.state_only_hiding.StateOnlyMaskMaterial
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × T0) := do
  let i := out
  if context.mask_layout_fingerprint != i
  then
    ok (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
      nonce_store)
  else
    let i1 ←
      aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
    if context.layout_factor_fingerprint != i1
    then
      ok (core.result.Result.Err
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
        nonce_store)
    else
      let r ←
        aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1
      let r1 ←
        core.result.Result.map_err
          (aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1StateOnlyMaskBuildError
          StateOnlyMaskNonceStoreInst) r ()
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let s := alloc.vec.Vec.deref val
        let r2 ←
          aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          aspis_prover.state_only_hiding.build_mask_material_for_layout
            StateOnlyMaskNonceStoreInst hash precommit_binding context
            private_entropy nonce_store s val1
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              aspis_prover.state_only_hiding.StateOnlyMaskMaterial
              (core.convert.FromSame
              aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
          ok (r3, nonce_store)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            aspis_prover.state_only_hiding.StateOnlyMaskMaterial
            (core.convert.FromSame
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
        ok (r2, nonce_store)


end R1Z.PV_RE_ComposedSuffix006
pv_composed_source_contexts ProverRwFull.aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix006.continueAfter
