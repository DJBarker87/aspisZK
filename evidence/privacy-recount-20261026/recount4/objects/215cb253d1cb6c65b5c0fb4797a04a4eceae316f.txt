import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwBodyStoreSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
def afterReserve
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
  (r : core.result.Result
    (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
      aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError)
  (nonce_store1 : T0) :
  Result ((core.result.Result ((alloc.vec.Vec Std.U8) ×
    prover.MaskedFixtureAudit) verifier.Error) × T0)
  := do
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
                          let i2 ← aspis_core.r0.merkle.C1_TAG
                          let r10 ←
                            prover.derive_private_salts reserved context hash
                              i2
                          let cf5 ←
                            core.result.Result.Insts.CoreOpsTry.branch r10
                          match cf5 with
                          | core.ops.control_flow.ControlFlow.Continue val5 =>
                            let i3 ← aspis_core.r0.merkle.C2_TAG
                            let r11 ←
                              prover.derive_private_salts reserved context hash
                                i3
                            let cf6 ←
                              core.result.Result.Insts.CoreOpsTry.branch r11
                            match cf6 with
                            | core.ops.control_flow.ControlFlow.Continue val6
                              =>
                              let r12 ← host_commitment.EncodingDomain.new
                              let r13 ←
                                core.result.Result.map_err
                                  (prover.prove_masked_with_attempt.closure_3.Insts.CoreOpsFunctionFnOnceTupleErrorError
                                  aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst)
                                  r12 ()
                              let cf7 ←
                                core.result.Result.Insts.CoreOpsTry.branch r13
                              match cf7 with
                              | core.ops.control_flow.ControlFlow.Continue val7
                                =>
                                let we ←
                                  aspis_core.field.wide_exact.WideExact.ZERO
                                let a := Array.repeat 1024#usize we
                                let v ←
                                  alloc.vec.from_elem (core.clone.CloneArray
                                    1024#usize
                                    aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone)
                                    a 29#usize
                                let (r14, backend) ←
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
                                    } hash variant
                                let r15 ←
                                  core.result.Result.map_err (BuiltinFnOnce
                                    r1_wire.Error verifier.Error) r14
                                    (prover.semantic_error)
                                let cf8 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r15
                                match cf8 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val8 =>
                                  let v1 ←
                                    Array.index_usize val8.columns 26#usize
                                  let s3 := alloc.vec.Vec.deref v1
                                  let o ←
                                    aspis_statement.state_only_semantic.state_only_copy_helper_sum
                                      s3
                                  let q ← aspis_core.field.QM31.ZERO
                                  let h1_total_balanced ←
                                    core.option.Option.Insts.CoreCmpPartialEqOption.eq
                                      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                      o (some q)
                                  if h1_total_balanced
                                  then
                                    let r16 ←
                                      prover.prove_from_semantics public1
                                        variant hash backend val8 (reserved,
                                        context)
                                    let cf9 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r16
                                    match cf9 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val9 =>
                                      ok (core.result.Result.Ok (val9,
                                        { audit with h1_total_balanced := true
                                        }), nonce_store1)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      let r17 ←
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          ((alloc.vec.Vec Std.U8) ×
                                          prover.MaskedFixtureAudit)
                                          (core.convert.FromSame
                                          verifier.Error) residual
                                      ok (r17, nonce_store1)
                                  else
                                    ok (core.result.Result.Err
                                      verifier.Error.Semantic, nonce_store1)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  let r16 ←
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      ((alloc.vec.Vec Std.U8) ×
                                      prover.MaskedFixtureAudit)
                                      (core.convert.FromSame verifier.Error)
                                      residual
                                  ok (r16, nonce_store1)
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                let r14 ←
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    ((alloc.vec.Vec Std.U8) ×
                                    prover.MaskedFixtureAudit)
                                    (core.convert.FromSame verifier.Error)
                                    residual
                                ok (r14, nonce_store1)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              let r12 ←
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  ((alloc.vec.Vec Std.U8) ×
                                  prover.MaskedFixtureAudit)
                                  (core.convert.FromSame verifier.Error)
                                  residual
                              ok (r12, nonce_store1)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r11 ←
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                ((alloc.vec.Vec Std.U8) ×
                                prover.MaskedFixtureAudit)
                                (core.convert.FromSame verifier.Error) residual
                            ok (r11, nonce_store1)
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
                ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
                (core.convert.FromSame verifier.Error) residual
            ok (r10, nonce_store1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r8 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
              (core.convert.FromSame verifier.Error) residual
          ok (r8, nonce_store1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r6 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
            (core.convert.FromSame verifier.Error) residual
        ok (r6, nonce_store1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r4 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
          (core.convert.FromSame verifier.Error) residual
      ok (r4, nonce_store1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual
    ok (r2, nonce_store1)
end R1Z.ProverRwBodyStoreSource
