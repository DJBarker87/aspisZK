import PV_EVH_Runtime
import PV_EVHB_CallbackSelection
set_option autoImplicit false
noncomputable section
namespace PV_EVHB_PrivateSaltStep
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Runtime (Q PartialView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  drop_OPEN : ∀ {T : Type}, T → Q Unit
  derive_pool_v1_leaf_salt_OPEN : ∀ (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (tree_tag : Std.U8) (leaf_index : Std.U32), Q ((core.result.Result (Array Std.U8 32#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError))

  push_OPEN : ∀ {T : Type} (v : alloc.vec.Vec T) (value : T), Q (alloc.vec.Vec T)

structure Compatible (c : Callees) : Prop where
  drop_fixed : ∀ {T : Type} (value : T), PartialView (c.drop_OPEN value) (.ok ())
  derive_pool_v1_leaf_salt_fixed : ∀ (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (tree_tag : Std.U8) (leaf_index : Std.U32), PartialView (c.derive_pool_v1_leaf_salt_OPEN self hash context tree_tag leaf_index) (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt self hash context tree_tag leaf_index)

  push_fixed : ∀ {T : Type} (v : alloc.vec.Vec T) (value : T), PartialView (c.push_OPEN v value) (alloc.vec.Vec.push v value)

def run
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (index : Std.U32)
  (salts : alloc.vec.Vec (Array Std.U8 32#usize)) (c : Callees) : Q (core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
    verifier.Error) := do
  let r ← c.derive_pool_v1_leaf_salt_OPEN
      reserved hash context tag index
  let r1 ← PV_EVHB_CallbackEffects.mapErr c.drop_OPEN c.drop_OPEN verifier.Error.Semantic r ()
  let cf ← PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let salts1 ← c.push_OPEN salts val
    pure (core.result.Result.Ok salts1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec (Array Std.U8 32#usize)) (core.convert.FromSame
      verifier.Error) residual)

theorem run_fixed
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (index : Std.U32)
  (salts : alloc.vec.Vec (Array Std.U8 32#usize)) (c : Callees) (compatible : Compatible c)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    PartialView (run reserved context hash tag index salts c) (prover.derive_private_salt_step reserved context hash tag index salts) := by
  unfold run prover.derive_private_salt_step
  try dsimp only
  apply PV_EVH_Runtime.bind_view
  ·
    exact compatible.derive_pool_v1_leaf_salt_fixed _ _ _ _ _
  · intro r
    try dsimp only
    apply PV_EVH_Runtime.bind_view
    ·
      change PartialView _ ((inferInstance : ExternalFuns).op12 _ _ _)
      exact PV_EVHB_CallbackSelection.constructor_mapErr_view _ selected _ c.drop_OPEN c.drop_OPEN verifier.Error.Semantic () _ (fun _ => rfl)
        (fun e => compatible.drop_fixed e) (compatible.drop_fixed ())
    · intro r1
      try dsimp only
      apply PV_EVH_Runtime.bind_view
      ·
        exact PV_EVH_Runtime.lift_view _
      · intro cf
        try dsimp only
        cases cf with
        | Continue val =>
          try dsimp only
          apply PV_EVH_Runtime.bind_view
          ·
            exact compatible.push_fixed _ _
          · intro salts1
            exact PV_EVH_Runtime.lift_view _
        | Break residual =>
          exact PV_EVH_Runtime.lift_view _

#print axioms run_fixed
end PV_EVHB_PrivateSaltStep
