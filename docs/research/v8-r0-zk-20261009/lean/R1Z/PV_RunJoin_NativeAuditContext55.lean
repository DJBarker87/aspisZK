import R1Z.PV_RunJoin_NativeAfterAudit55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeAuditContext55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
variable [ExternalTypes] [ExternalFuns]
def run {A : Type} (publish : Phase → Result (core.result.Result A verifier.Error))
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (binding : Array Std.U8 32#usize)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store : T0) :
  Result ((core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error) × T0)
  := do
  let (r, nonce_store1) ←
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst attempt hash
      binding context nonce_store
  let r1 ←
    core.result.Result.map_err (BuiltinFnOnce
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError verifier.Error) r
      (prover.mask_error)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (reserved, material) := val
    let noised_c1 ←
      aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
        compiled.semantic_c1
    let (r2, noised_c11) ←
      aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
        noised_c1 material
    let r3 ←
      core.result.Result.map_err
        (prover.prove_masked_with_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
        aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r2 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r4 ←
        aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1
      let r5 ←
        core.result.Result.map_err
          (prover.prove_masked_with_attempt.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error
          aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r4 ()
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r5
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r6 ←
          aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d
            reserved hash context
        let r7 ←
          core.result.Result.map_err (BuiltinFnOnce
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError
            verifier.Error) r6 (prover.mask_error)
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r7
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r8 ←
            Array.Insts.CoreConvertTryFromVecVec.try_from Global 1024#usize
              val3
          let r9 ←
            core.result.Result.map_err
              (prover.prove_masked_with_attempt.closure_2.Insts.CoreOpsFunctionFnOnceTupleVecQM31Error
              aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r8 ()
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r9
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let i := alloc.vec.Vec.len val1.g
            if i != 1024#usize
            then
              ok (core.result.Result.Err verifier.Error.Semantic, nonce_store1)
            else
              let i1 := alloc.vec.Vec.len val1.h1_padding
              if i1 != 1024#usize
              then
                ok (core.result.Result.Err verifier.Error.Semantic,
                  nonce_store1)
              else
                let s := alloc.vec.Vec.deref val1.g
                let g ← prover.fixed_k_column s
                let s1 := alloc.vec.Vec.deref val1.h1_padding
                let h1_padding ← prover.fixed_k_column s1
                let s2 ← Aeneas.Std.lift (Array.to_slice noised_c11.c1)
                let audit ←
                  prover.audit_masks s2 val1.mask_only_c1 val4 g h1_padding
                    val2
                if audit.c1_columns_inactive_balanced != 16#usize
                then
                  ok (core.result.Result.Err verifier.Error.Semantic,
                    nonce_store1)
                else
                  if audit.mask_only_columns_inactive_balanced != 10#usize
                  then
                    ok (core.result.Result.Err verifier.Error.Semantic,
                      nonce_store1)
                  else
                    if audit.d_inactive_balanced
                    then
                      if audit.g_inactive_balanced
                      then
                        if audit.h1_padding_inactive_balanced
                        then
                          PV_RunJoin_NativeAfterAudit55.run publish aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash reserved context noised_c11 val1.mask_only_c1 val4 g h1_padding audit nonce_store1
                        else
                          ok (core.result.Result.Err verifier.Error.Semantic,
                            nonce_store1)
                      else
                        ok (core.result.Result.Err verifier.Error.Semantic,
                          nonce_store1)
                    else
                      ok (core.result.Result.Err verifier.Error.Semantic,
                        nonce_store1)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r10 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (A × prover.MaskedFixtureAudit)
                (core.convert.FromSame verifier.Error) residual
            ok (r10, nonce_store1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r8 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (A × prover.MaskedFixtureAudit)
              (core.convert.FromSame verifier.Error) residual
          ok (r8, nonce_store1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r6 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (A × prover.MaskedFixtureAudit)
            (core.convert.FromSame verifier.Error) residual
        ok (r6, nonce_store1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r4 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (A × prover.MaskedFixtureAudit)
          (core.convert.FromSame verifier.Error) residual
      ok (r4, nonce_store1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (A × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual
    ok (r2, nonce_store1)

#print axioms run
end R1Z.PV_RunJoin_NativeAuditContext55
