import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_PrivateSaltStep
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Hash)
  (tag : Std.U8) (index : Std.U32)
  (salts : alloc.vec.Vec (Array Std.U8 32#usize)) :
  P (core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
    verifier.Error) := do
  let r ← invoke "aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
      reserved hash context tag index)
  let r1 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.map_err
      prover.derive_private_salt_step.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
      r ())
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let salts1 ← invoke "alloc.vec.Vec.push" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        alloc.vec.Vec.push salts val)
    pure (core.result.Result.Ok salts1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec (Array Std.U8 32#usize)) (core.convert.FromSame
      verifier.Error) residual)

theorem erase_program (ops : ExternalFuns)
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Hash)
  (tag : Std.U8) (index : Std.U32)
  (salts : alloc.vec.Vec (Array Std.U8 32#usize)) :
  erase ops (program reserved context hash tag index salts) =
    @prover.derive_private_salt_step _ ops reserved context (sourceHash ops hash) tag index salts := by
  unfold program prover.derive_private_salt_step
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
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro salts1
            rfl
        | Break residual =>
          exact erase_invoke ops _ _

#print axioms erase_program
end R1Z.PV_W_R_PrivateSaltStep
