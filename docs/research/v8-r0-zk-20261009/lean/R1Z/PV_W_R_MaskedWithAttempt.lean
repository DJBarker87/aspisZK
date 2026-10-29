import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
import R1Z.PV_W_R_ApplyMaterial
import R1Z.PV_W_R_AuditMasks
import R1Z.PV_W_R_FixedColumn
import R1Z.PV_W_R_FromSemantics
import R1Z.PV_W_R_PrivateSalts
import R1Z.PV_W_R_ReserveBuild
import R1Z.PV_W_R_ZeroFactor
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_MaskedWithAttempt
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst : Store T0)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Hash)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (binding : Array Std.U8 32#usize)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store : T0) :
  P ((core.result.Result ((alloc.vec.Vec Std.U8) ×
    prover.MaskedFixtureAudit) verifier.Error) × T0) := do
  let (r, nonce_store1) ← PV_W_R_ReserveBuild.program
    aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst attempt hash
    binding context nonce_store
  let r1 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
      core.result.Result.map_err (BuiltinFnOnce
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError verifier.Error) r
      (prover.mask_error))
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
      core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (reserved, material) := val
    let noised_c1 ← invoke "aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
        aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
        compiled.semantic_c1)
    let (r2, noised_c11) ← PV_W_R_ApplyMaterial.program
      noised_c1 material
    let r3 ← invoke "core.result.Result.map_err" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
        core.result.Result.map_err
        (prover.prove_masked_with_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
        aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r2 ())
    let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
        core.result.Result.Insts.CoreOpsTry.branch r3)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r4 ← invoke "aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
          aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1)
      let r5 ← invoke "core.result.Result.map_err" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
          core.result.Result.map_err
          (prover.prove_masked_with_attempt.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error
          aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r4 ())
      let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
          core.result.Result.Insts.CoreOpsTry.branch r5)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r6 ← PV_W_R_ZeroFactor.program
          reserved hash context
        let r7 ← invoke "core.result.Result.map_err" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
            core.result.Result.map_err (BuiltinFnOnce
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError
            verifier.Error) r6 (prover.mask_error))
        let cf3 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
            core.result.Result.Insts.CoreOpsTry.branch r7)
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r8 ← invoke "Array.Insts.CoreConvertTryFromVecVec.try_from" (fun ops =>
              letI : ExternalFuns := ops
              let hash := sourceHash ops hash
              let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
              Array.Insts.CoreConvertTryFromVecVec.try_from Global 1024#usize
              val3)
          let r9 ← invoke "core.result.Result.map_err" (fun ops =>
              letI : ExternalFuns := ops
              let hash := sourceHash ops hash
              let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
              core.result.Result.map_err
              (prover.prove_masked_with_attempt.closure_2.Insts.CoreOpsFunctionFnOnceTupleVecQM31Error
              aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r8 ())
          let cf4 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
              letI : ExternalFuns := ops
              let hash := sourceHash ops hash
              let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
              core.result.Result.Insts.CoreOpsTry.branch r9)
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let i := alloc.vec.Vec.len val1.g
            if i != 1024#usize then
              pure (core.result.Result.Err verifier.Error.Semantic, nonce_store1)
            else
              let i1 := alloc.vec.Vec.len val1.h1_padding
              if i1 != 1024#usize then
                pure (core.result.Result.Err verifier.Error.Semantic,
                  nonce_store1)
              else
                let s := alloc.vec.Vec.deref val1.g
                let g ← PV_W_R_FixedColumn.program s
                let s1 := alloc.vec.Vec.deref val1.h1_padding
                let h1_padding ← PV_W_R_FixedColumn.program s1
                let s2 ← invoke "Aeneas.Std.lift" (fun ops =>
                    letI : ExternalFuns := ops
                    let hash := sourceHash ops hash
                    let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                    Aeneas.Std.lift (Array.to_slice noised_c11.c1))
                let audit ← PV_W_R_AuditMasks.program s2 val1.mask_only_c1 val4 g h1_padding
                  val2
                if audit.c1_columns_inactive_balanced != 16#usize then
                  pure (core.result.Result.Err verifier.Error.Semantic,
                    nonce_store1)
                else
                  if audit.mask_only_columns_inactive_balanced != 10#usize then
                    pure (core.result.Result.Err verifier.Error.Semantic,
                      nonce_store1)
                  else
                    if audit.d_inactive_balanced then
                      if audit.g_inactive_balanced then
                        if audit.h1_padding_inactive_balanced then
                          let i2 ← invoke "aspis_core.r0.merkle.C1_TAG" (fun ops =>
                              letI : ExternalFuns := ops
                              let hash := sourceHash ops hash
                              let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                              aspis_core.r0.merkle.C1_TAG)
                          let r10 ← PV_W_R_PrivateSalts.program reserved context hash
                            i2
                          let cf5 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                              letI : ExternalFuns := ops
                              let hash := sourceHash ops hash
                              let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                              core.result.Result.Insts.CoreOpsTry.branch r10)
                          match cf5 with
                          | core.ops.control_flow.ControlFlow.Continue val5 =>
                            let i3 ← invoke "aspis_core.r0.merkle.C2_TAG" (fun ops =>
                                letI : ExternalFuns := ops
                                let hash := sourceHash ops hash
                                let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                aspis_core.r0.merkle.C2_TAG)
                            let r11 ← PV_W_R_PrivateSalts.program reserved context hash
                              i3
                            let cf6 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                letI : ExternalFuns := ops
                                let hash := sourceHash ops hash
                                let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                core.result.Result.Insts.CoreOpsTry.branch r11)
                            match cf6 with
                            | core.ops.control_flow.ControlFlow.Continue val6 =>
                              let r12 ← invoke "host_commitment.EncodingDomain.new" (fun ops =>
                                  letI : ExternalFuns := ops
                                  let hash := sourceHash ops hash
                                  let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                  host_commitment.EncodingDomain.new)
                              let r13 ← invoke "core.result.Result.map_err" (fun ops =>
                                  letI : ExternalFuns := ops
                                  let hash := sourceHash ops hash
                                  let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                  core.result.Result.map_err
                                  (prover.prove_masked_with_attempt.closure_3.Insts.CoreOpsFunctionFnOnceTupleErrorError
                                  aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst)
                                  r12 ())
                              let cf7 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                  letI : ExternalFuns := ops
                                  let hash := sourceHash ops hash
                                  let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                  core.result.Result.Insts.CoreOpsTry.branch r13)
                              match cf7 with
                              | core.ops.control_flow.ControlFlow.Continue val7 =>
                                let we ← invoke "aspis_core.field.wide_exact.WideExact.ZERO" (fun ops =>
                                    letI : ExternalFuns := ops
                                    let hash := sourceHash ops hash
                                    let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                    aspis_core.field.wide_exact.WideExact.ZERO)
                                let a := Array.repeat 1024#usize we
                                let v ← invoke "alloc.vec.from_elem" (fun ops =>
                                    letI : ExternalFuns := ops
                                    let hash := sourceHash ops hash
                                    let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                    alloc.vec.from_elem (core.clone.CloneArray
                                    1024#usize
                                    aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone)
                                    a 29#usize)
                                let (r14, backend) ← invoke "host_semantic.build_with_material" (fun ops =>
                                    letI : ExternalFuns := ops
                                    let hash := sourceHash ops hash
                                    let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                    host_semantic.build_with_material
                                    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
                                    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
                                    public1 compiled noised_c11
                                    val1.mask_only_c1 val4 g h1_padding
                                    {
                                    hash,
                                    variant,
                                    domain := val7,
                                    messages := v,
                                    c1 := none,
                                    c2 := none,
                                    c1_salts := (some val5),
                                    c2_salts := (some val6)
                                    } hash variant)
                                let r15 ← invoke "core.result.Result.map_err" (fun ops =>
                                    letI : ExternalFuns := ops
                                    let hash := sourceHash ops hash
                                    let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                    core.result.Result.map_err (BuiltinFnOnce
                                    r1_wire.Error verifier.Error) r14
                                    (prover.semantic_error))
                                let cf8 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                    letI : ExternalFuns := ops
                                    let hash := sourceHash ops hash
                                    let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                    core.result.Result.Insts.CoreOpsTry.branch
                                    r15)
                                match cf8 with
                                | core.ops.control_flow.ControlFlow.Continue val8 =>
                                  let v1 ← invoke "Array.index_usize" (fun ops =>
                                      letI : ExternalFuns := ops
                                      let hash := sourceHash ops hash
                                      let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                      Array.index_usize val8.columns 26#usize)
                                  let s3 := alloc.vec.Vec.deref v1
                                  let o ← invoke "aspis_statement.state_only_semantic.state_only_copy_helper_sum" (fun ops =>
                                      letI : ExternalFuns := ops
                                      let hash := sourceHash ops hash
                                      let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                      aspis_statement.state_only_semantic.state_only_copy_helper_sum
                                      s3)
                                  let q ← invoke "aspis_core.field.QM31.ZERO" (fun ops =>
                                      letI : ExternalFuns := ops
                                      let hash := sourceHash ops hash
                                      let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                      aspis_core.field.QM31.ZERO)
                                  let h1_total_balanced ← invoke "core.option.Option.Insts.CoreCmpPartialEqOption.eq" (fun ops =>
                                      letI : ExternalFuns := ops
                                      let hash := sourceHash ops hash
                                      let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                      core.option.Option.Insts.CoreCmpPartialEqOption.eq
                                      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                      o (some q))
                                  if h1_total_balanced then
                                    let r16 ← PV_W_R_FromSemantics.program public1
                                      variant hash backend val8 (reserved,
                                      context)
                                    let cf9 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                        letI : ExternalFuns := ops
                                        let hash := sourceHash ops hash
                                        let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                        core.result.Result.Insts.CoreOpsTry.branch
                                        r16)
                                    match cf9 with
                                    | core.ops.control_flow.ControlFlow.Continue val9 =>
                                      pure (core.result.Result.Ok (val9,
                                        { audit with h1_total_balanced := true
                                        }), nonce_store1)
                                    | core.ops.control_flow.ControlFlow.Break residual =>
                                      let r17 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                          letI : ExternalFuns := ops
                                          let hash := sourceHash ops hash
                                          let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          ((alloc.vec.Vec Std.U8) ×
                                          prover.MaskedFixtureAudit)
                                          (core.convert.FromSame
                                          verifier.Error) residual)
                                      pure (r17, nonce_store1)
                                  else
                                    pure (core.result.Result.Err
                                      verifier.Error.Semantic, nonce_store1)
                                | core.ops.control_flow.ControlFlow.Break residual =>
                                  let r16 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                      letI : ExternalFuns := ops
                                      let hash := sourceHash ops hash
                                      let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      ((alloc.vec.Vec Std.U8) ×
                                      prover.MaskedFixtureAudit)
                                      (core.convert.FromSame verifier.Error)
                                      residual)
                                  pure (r16, nonce_store1)
                              | core.ops.control_flow.ControlFlow.Break residual =>
                                let r14 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                    letI : ExternalFuns := ops
                                    let hash := sourceHash ops hash
                                    let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    ((alloc.vec.Vec Std.U8) ×
                                    prover.MaskedFixtureAudit)
                                    (core.convert.FromSame verifier.Error)
                                    residual)
                                pure (r14, nonce_store1)
                            | core.ops.control_flow.ControlFlow.Break residual =>
                              let r12 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                  letI : ExternalFuns := ops
                                  let hash := sourceHash ops hash
                                  let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  ((alloc.vec.Vec Std.U8) ×
                                  prover.MaskedFixtureAudit)
                                  (core.convert.FromSame verifier.Error)
                                  residual)
                              pure (r12, nonce_store1)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r11 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                letI : ExternalFuns := ops
                                let hash := sourceHash ops hash
                                let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                ((alloc.vec.Vec Std.U8) ×
                                prover.MaskedFixtureAudit)
                                (core.convert.FromSame verifier.Error) residual)
                            pure (r11, nonce_store1)
                        else
                          pure (core.result.Result.Err verifier.Error.Semantic,
                            nonce_store1)
                      else
                        pure (core.result.Result.Err verifier.Error.Semantic,
                          nonce_store1)
                    else
                      pure (core.result.Result.Err verifier.Error.Semantic,
                        nonce_store1)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r10 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                letI : ExternalFuns := ops
                let hash := sourceHash ops hash
                let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
                (core.convert.FromSame verifier.Error) residual)
            pure (r10, nonce_store1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r8 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
              letI : ExternalFuns := ops
              let hash := sourceHash ops hash
              let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
              (core.convert.FromSame verifier.Error) residual)
          pure (r8, nonce_store1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r6 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
            (core.convert.FromSame verifier.Error) residual)
        pure (r6, nonce_store1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r4 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
          (core.convert.FromSame verifier.Error) residual)
      pure (r4, nonce_store1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        let aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual)
    pure (r2, nonce_store1)

theorem erase_program (ops : ExternalFuns)
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst : Store T0)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Hash)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (binding : Array Std.U8 32#usize)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store : T0) :
  erase ops (program aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash context binding attempt nonce_store) =
    @prover.prove_masked_with_attempt _ ops T0 (sourceStore ops aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) public1 compiled variant (sourceHash ops hash) context binding attempt nonce_store := by
  unfold program prover.prove_masked_with_attempt
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    rw [PV_W_R_ReserveBuild.erase_program]
  · rintro ⟨r, nonce_store1⟩
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
          · intro noised_c1
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              rw [PV_W_R_ApplyMaterial.erase_program]
            · rintro ⟨r2, noised_c11⟩
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · intro r3
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
                      exact erase_invoke ops _ _
                    · intro r4
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact erase_invoke ops _ _
                      · intro r5
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro cf2
                          try dsimp only
                          cases cf2 with
                          | Continue val2 =>
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              rw [PV_W_R_ZeroFactor.erase_program]
                            · intro r6
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact erase_invoke ops _ _
                              · intro r7
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro cf3
                                  try dsimp only
                                  cases cf3 with
                                  | Continue val3 =>
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact erase_invoke ops _ _
                                    · intro r8
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
                                      · intro r9
                                        try dsimp only
                                        rw [erase_bind]
                                        apply PV_W_RecursiveLaws.bind_congr
                                        ·
                                          exact erase_invoke ops _ _
                                        · intro cf4
                                          try dsimp only
                                          cases cf4 with
                                          | Continue val4 =>
                                            try dsimp only
                                            try dsimp only
                                            apply PV_W_Callbacks.erase_if_congr
                                            ·
                                              rfl
                                            ·
                                              try dsimp only
                                              try dsimp only
                                              apply PV_W_Callbacks.erase_if_congr
                                              ·
                                                rfl
                                              ·
                                                try dsimp only
                                                try dsimp only
                                                rw [erase_bind]
                                                apply PV_W_RecursiveLaws.bind_congr
                                                ·
                                                  rw [PV_W_R_FixedColumn.erase_program]
                                                · intro g
                                                  try dsimp only
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    rw [PV_W_R_FixedColumn.erase_program]
                                                  · intro h1_padding
                                                    try dsimp only
                                                    rw [erase_bind]
                                                    apply PV_W_RecursiveLaws.bind_congr
                                                    ·
                                                      exact erase_invoke ops _ _
                                                    · intro s2
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        rw [PV_W_R_AuditMasks.erase_program]
                                                      · intro audit
                                                        try dsimp only
                                                        apply PV_W_Callbacks.erase_if_congr
                                                        ·
                                                          rfl
                                                        ·
                                                          try dsimp only
                                                          apply PV_W_Callbacks.erase_if_congr
                                                          ·
                                                            rfl
                                                          ·
                                                            try dsimp only
                                                            apply PV_W_Callbacks.erase_if_congr
                                                            ·
                                                              try dsimp only
                                                              apply PV_W_Callbacks.erase_if_congr
                                                              ·
                                                                try dsimp only
                                                                apply PV_W_Callbacks.erase_if_congr
                                                                ·
                                                                  try dsimp only
                                                                  rw [erase_bind]
                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                  ·
                                                                    exact erase_invoke ops _ _
                                                                  · intro i2
                                                                    try dsimp only
                                                                    rw [erase_bind]
                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                    ·
                                                                      rw [PV_W_R_PrivateSalts.erase_program]
                                                                    · intro r10
                                                                      try dsimp only
                                                                      rw [erase_bind]
                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                      ·
                                                                        exact erase_invoke ops _ _
                                                                      · intro cf5
                                                                        try dsimp only
                                                                        cases cf5 with
                                                                        | Continue val5 =>
                                                                          try dsimp only
                                                                          rw [erase_bind]
                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                          ·
                                                                            exact erase_invoke ops _ _
                                                                          · intro i3
                                                                            try dsimp only
                                                                            rw [erase_bind]
                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                            ·
                                                                              rw [PV_W_R_PrivateSalts.erase_program]
                                                                            · intro r11
                                                                              try dsimp only
                                                                              rw [erase_bind]
                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                              ·
                                                                                exact erase_invoke ops _ _
                                                                              · intro cf6
                                                                                try dsimp only
                                                                                cases cf6 with
                                                                                | Continue val6 =>
                                                                                  try dsimp only
                                                                                  rw [erase_bind]
                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                  ·
                                                                                    exact erase_invoke ops _ _
                                                                                  · intro r12
                                                                                    try dsimp only
                                                                                    rw [erase_bind]
                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                    ·
                                                                                      exact erase_invoke ops _ _
                                                                                    · intro r13
                                                                                      try dsimp only
                                                                                      rw [erase_bind]
                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                      ·
                                                                                        exact erase_invoke ops _ _
                                                                                      · intro cf7
                                                                                        try dsimp only
                                                                                        cases cf7 with
                                                                                        | Continue val7 =>
                                                                                          try dsimp only
                                                                                          rw [erase_bind]
                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                          ·
                                                                                            exact erase_invoke ops _ _
                                                                                          · intro we
                                                                                            try dsimp only
                                                                                            try dsimp only
                                                                                            rw [erase_bind]
                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                            ·
                                                                                              exact erase_invoke ops _ _
                                                                                            · intro v
                                                                                              try dsimp only
                                                                                              rw [erase_bind]
                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                              ·
                                                                                                exact erase_invoke ops _ _
                                                                                              · rintro ⟨r14, backend⟩
                                                                                                try dsimp only
                                                                                                rw [erase_bind]
                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                ·
                                                                                                  exact erase_invoke ops _ _
                                                                                                · intro r15
                                                                                                  try dsimp only
                                                                                                  rw [erase_bind]
                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                  ·
                                                                                                    exact erase_invoke ops _ _
                                                                                                  · intro cf8
                                                                                                    try dsimp only
                                                                                                    cases cf8 with
                                                                                                    | Continue val8 =>
                                                                                                      try dsimp only
                                                                                                      rw [erase_bind]
                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                      ·
                                                                                                        exact erase_invoke ops _ _
                                                                                                      · intro v1
                                                                                                        try dsimp only
                                                                                                        try dsimp only
                                                                                                        rw [erase_bind]
                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                        ·
                                                                                                          exact erase_invoke ops _ _
                                                                                                        · intro o
                                                                                                          try dsimp only
                                                                                                          rw [erase_bind]
                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                          ·
                                                                                                            exact erase_invoke ops _ _
                                                                                                          · intro q
                                                                                                            try dsimp only
                                                                                                            rw [erase_bind]
                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                            ·
                                                                                                              exact erase_invoke ops _ _
                                                                                                            · intro h1_total_balanced
                                                                                                              try dsimp only
                                                                                                              apply PV_W_Callbacks.erase_if_congr
                                                                                                              ·
                                                                                                                try dsimp only
                                                                                                                rw [erase_bind]
                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                ·
                                                                                                                  rw [PV_W_R_FromSemantics.erase_program]
                                                                                                                · intro r16
                                                                                                                  try dsimp only
                                                                                                                  rw [erase_bind]
                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                  ·
                                                                                                                    exact erase_invoke ops _ _
                                                                                                                  · intro cf9
                                                                                                                    try dsimp only
                                                                                                                    cases cf9 with
                                                                                                                    | Continue val9 =>
                                                                                                                      rfl
                                                                                                                    | Break residual =>
                                                                                                                      try dsimp only
                                                                                                                      rw [erase_bind]
                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                      ·
                                                                                                                        exact erase_invoke ops _ _
                                                                                                                      · intro r17
                                                                                                                        rfl
                                                                                                              ·
                                                                                                                rfl
                                                                                                    | Break residual =>
                                                                                                      try dsimp only
                                                                                                      rw [erase_bind]
                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                      ·
                                                                                                        exact erase_invoke ops _ _
                                                                                                      · intro r16
                                                                                                        rfl
                                                                                        | Break residual =>
                                                                                          try dsimp only
                                                                                          rw [erase_bind]
                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                          ·
                                                                                            exact erase_invoke ops _ _
                                                                                          · intro r14
                                                                                            rfl
                                                                                | Break residual =>
                                                                                  try dsimp only
                                                                                  rw [erase_bind]
                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                  ·
                                                                                    exact erase_invoke ops _ _
                                                                                  · intro r12
                                                                                    rfl
                                                                        | Break residual =>
                                                                          try dsimp only
                                                                          rw [erase_bind]
                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                          ·
                                                                            exact erase_invoke ops _ _
                                                                          · intro r11
                                                                            rfl
                                                                ·
                                                                  rfl
                                                              ·
                                                                rfl
                                                            ·
                                                              rfl
                                          | Break residual =>
                                            try dsimp only
                                            rw [erase_bind]
                                            apply PV_W_RecursiveLaws.bind_congr
                                            ·
                                              exact erase_invoke ops _ _
                                            · intro r10
                                              rfl
                                  | Break residual =>
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact erase_invoke ops _ _
                                    · intro r8
                                      rfl
                          | Break residual =>
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              exact erase_invoke ops _ _
                            · intro r6
                              rfl
                  | Break residual =>
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro r4
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
end R1Z.PV_W_R_MaskedWithAttempt
