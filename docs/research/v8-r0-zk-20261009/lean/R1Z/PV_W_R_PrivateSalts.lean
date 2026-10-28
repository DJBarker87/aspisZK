import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_PrivateSalts
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Hash)
  (tag : Std.U8) :
  P (core.result.Result host_commitment.PrivateSalts verifier.Error) := do
  let count ← invoke "aspis_core.r0.FIBRE_COUNT" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      aspis_core.r0.FIBRE_COUNT)
  let (r, salts) ← perform (.reserve Global (alloc.vec.Vec.new (Array Std.U8
32#usize)) count)
  let r1 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.map_err
      prover.derive_private_salts.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError
      r ())
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let result ← invoke "prover.derive_private_salts_loop" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        prover.derive_private_salts_loop reserved context hash tag count
        (core.result.Result.Ok salts) 0#usize)
    invoke "core.result.Result.map" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.map (BuiltinFnOnce (alloc.vec.Vec (Array Std.U8
      32#usize)) host_commitment.PrivateSalts) result
      (host_commitment.PrivateSalts.new))
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      host_commitment.PrivateSalts (core.convert.FromSame verifier.Error)
      residual)

theorem erase_program (ops : ExternalFuns)
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Hash)
  (tag : Std.U8) :
  erase ops (program reserved context hash tag) =
    @prover.derive_private_salts _ ops reserved context (sourceHash ops hash) tag := by
  unfold program prover.derive_private_salts
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro count
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_perform ops _
    · rintro ⟨r, salts⟩
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
          | Continue unused0_0 =>
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro result
              exact erase_invoke ops _ _
          | Break residual =>
            exact erase_invoke ops _ _

#print axioms erase_program
end R1Z.PV_W_R_PrivateSalts
