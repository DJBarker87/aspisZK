import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OpPrivateSaltStep
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  derive_pool_v1_leaf_salt_OPEN : ∀ (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (tree_tag : Std.U8) (leaf_index : Std.U32), P ((core.result.Result (Array Std.U8 32#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError))
  op12_OPEN : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
      core.ops.function.FnOnce O E F) (arg0 : (core.result.Result T E)) (arg1 : O), P ((core.result.Result T F))
  push_OPEN : ∀ {T : Type} (v : alloc.vec.Vec T) (value : T), P (alloc.vec.Vec T)

structure Compatible (c : Callees) : Prop where
  derive_pool_v1_leaf_salt_fixed : ∀ (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (tree_tag : Std.U8) (leaf_index : Std.U32), FinishedView (c.derive_pool_v1_leaf_salt_OPEN self hash context tree_tag leaf_index) (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt self hash context tree_tag leaf_index)
  op12_fixed : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
      core.ops.function.FnOnce O E F) (arg0 : (core.result.Result T E)) (arg1 : O), FinishedView (c.op12_OPEN opsfunctionFnOnceOTupleEFInst arg0 arg1) (core.result.Result.map_err opsfunctionFnOnceOTupleEFInst arg0 arg1)
  push_fixed : ∀ {T : Type} (v : alloc.vec.Vec T) (value : T), FinishedView (c.push_OPEN v value) (alloc.vec.Vec.push v value)

def run
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (index : Std.U32)
  (salts : alloc.vec.Vec (Array Std.U8 32#usize)) (c : Callees) : P (core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
    verifier.Error) := do
  let r ← c.derive_pool_v1_leaf_salt_OPEN
      reserved hash context tag index
  let r1 ← c.op12_OPEN
      prover.derive_private_salt_step.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
      r ()
  let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let salts1 ← c.push_OPEN salts val
    pure (core.result.Result.Ok salts1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec (Array Std.U8 32#usize)) (core.convert.FromSame
      verifier.Error) residual)

theorem run_fixed
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (index : Std.U32)
  (salts : alloc.vec.Vec (Array Std.U8 32#usize)) (c : Callees) (compatible : Compatible c) :
    FinishedView (run reserved context hash tag index salts c) (prover.derive_private_salt_step reserved context hash tag index salts) := by
  unfold run prover.derive_private_salt_step
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact compatible.derive_pool_v1_leaf_salt_fixed _ _ _ _ _
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
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact compatible.push_fixed _ _
          · intro salts1
            exact PV_EVH_Prefix.lift_fixed _
        | Break residual =>
          exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_OpPrivateSaltStep
