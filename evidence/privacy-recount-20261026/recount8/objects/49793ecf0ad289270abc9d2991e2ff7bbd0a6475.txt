import R1Z.PV_RJDec_MaskedWithAttempt
import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
import R1Z.PV_W_R_DurableReserve
import R1Z.PV_W_R_MaskedWithAttempt
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Entry
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Hash)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
  P ((core.result.Result ((alloc.vec.Vec Std.U8) ×
    prover.MaskedFixtureAudit) verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let r ← invoke "aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      public1)
  let r1 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.map_err
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      r ())
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let s1 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ s ])))
    let a ← hash s1
    let a1 ← invoke "aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.impl.mask_nonce" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.impl.mask_nonce
        attempt)
    let context ← invoke "aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1
        a a1)
    let s2 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        Aeneas.Std.lift (Array.to_slice
        (Array.make 30#usize [
        85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
        49#u8, 58#u8, 80#u8, 51#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8,
        84#u8, 69#u8, 45#u8, 65#u8, 84#u8, 84#u8, 69#u8, 77#u8, 80#u8, 84#u8
        ])))
    let s3 := alloc.vec.Vec.deref val
    let i ← invoke "transport.Variant.tag" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        transport.Variant.tag variant)
    let s4 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ i ])))
    let a2 ← invoke "aspis_core.state_only_hiding.StateOnlyHidingContext.encode" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        aspis_core.state_only_hiding.StateOnlyHidingContext.encode context)
    let s5 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        Aeneas.Std.lift (Array.to_slice a2))
    let s6 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        Aeneas.Std.lift (Array.to_slice (Array.make 4#usize [ s2, s3, s4, s5 ])))
    let binding ← hash s6
    (PV_RJDec_MaskedWithAttempt.program
      PV_W_R_DurableReserve.store
      public1 compiled variant hash context binding attempt nonce_store)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual)
    pure (r2, nonce_store)

theorem erase_program (ops : ExternalFuns)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Hash)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
  erase (PV_RJDec_ZeroizingSelected.selected ops) (program public1 compiled variant hash attempt nonce_store) =
    @prover.prove_masked_attempt _ (PV_RJDec_ZeroizingSelected.selected ops) public1 compiled variant (sourceHash (PV_RJDec_ZeroizingSelected.selected ops) hash) attempt nonce_store := by
  unfold program prover.prove_masked_attempt
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
  · intro r
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
    · intro r1
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
      · intro cf
        try dsimp only
        cases cf with
        | Continue val =>
          try dsimp only
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
          · intro s1
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              rfl
            · intro a
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
              · intro a1
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
                · intro context
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
                  · intro s2
                    try dsimp only
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
                    · intro i
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
                      · intro s4
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
                        · intro a2
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
                          · intro s5
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
                            · intro s6
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                rfl
                              · intro binding
                                rw [PV_RJDec_MaskedWithAttempt.erase_program,PV_W_R_DurableReserve.store_source]
        | Break residual =>
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _
          · intro r2
            rfl

#print axioms erase_program
end R1Z.PV_RJDec_Entry
