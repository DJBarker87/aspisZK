import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
import R1Z.PV_W_R_FinishOpening
import R1Z.PV_W_R_PrepareOpening
import R1Z.PV_W_R_PrivateSalts
import R1Z.PV_W_R_PublishCompact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_FromSemantics
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Hash)
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_core.state_only_hiding.StateOnlyHidingContext)) :
  P (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error) := do
  let (reserved, context) := salts
  let r ← PV_W_R_PrepareOpening.program variant hash backend sem
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← PV_W_R_PrivateSalts.program reserved context hash 114#u8
    let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ← PV_W_R_FinishOpening.program variant hash val val1
      let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        PV_W_R_PublishCompact.program variant val2
      | core.ops.control_flow.ControlFlow.Break residual =>
        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual)

theorem erase_program (ops : ExternalFuns)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Hash)
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_core.state_only_hiding.StateOnlyHidingContext)) :
  erase ops (program public1 variant hash backend sem salts) =
    @prover.prove_from_semantics _ ops public1 variant (sourceHash ops hash) backend sem salts := by
  unfold program prover.prove_from_semantics
  try dsimp only
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    rw [PV_W_R_PrepareOpening.erase_program]
  · intro r
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
          rw [PV_W_R_PrivateSalts.erase_program]
        · intro r1
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro cf1
            try dsimp only
            cases cf1 with
            | Continue val1 =>
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                rw [PV_W_R_FinishOpening.erase_program]
              · intro r2
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro cf2
                  try dsimp only
                  cases cf2 with
                  | Continue val2 =>
                    rw [PV_W_R_PublishCompact.erase_program]
                  | Break residual =>
                    exact erase_invoke ops _ _
            | Break residual =>
              exact erase_invoke ops _ _
      | Break residual =>
        exact erase_invoke ops _ _

#print axioms erase_program
end R1Z.PV_W_R_FromSemantics
