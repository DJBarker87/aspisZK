import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_030
import PV_L1D_Source_031
import PV_L1D_Source_037
import PV_L1D_Source_068
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_069
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
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
  Logged ((core.result.Result ((alloc.vec.Vec Std.U8) ×
    prover.MaskedFixtureAudit) verifier.Error) × T0)
  := do
  let _ ← observe .callback 0 (ok ())
  let (r, nonce_store1) ← PV_L1D_Logged.lift (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst attempt hash
      binding context nonce_store)
  let r1 ← PV_L1D_Logged.lift (core.result.Result.map_err (BuiltinFnOnce
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError verifier.Error) r
      (prover.mask_error))
  let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (reserved, material) := val
    let noised_c1 ← PV_L1D_Logged.lift (aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
        compiled.semantic_c1)
    let (r2, noised_c11) ← PV_L1D_Logged.lift (aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
        noised_c1 material)
    let r3 ← PV_L1D_Logged.lift (core.result.Result.map_err
        (prover.prove_masked_with_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
        aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r2 ())
    let cf1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r3)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r4 ← PV_L1D_Logged.lift (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1)
      let r5 ← PV_L1D_Logged.lift (core.result.Result.map_err
          (prover.prove_masked_with_attempt.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error
          aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r4 ())
      let cf2 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r5)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r6 ← PV_L1D_Logged.lift (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d
            reserved hash context)
        let r7 ← PV_L1D_Logged.lift (core.result.Result.map_err (BuiltinFnOnce
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError
            verifier.Error) r6 (prover.mask_error))
        let cf3 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r7)
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r8 ← PV_L1D_Logged.lift (Array.Insts.CoreConvertTryFromVecVec.try_from Global 1024#usize
              val3)
          let r9 ← PV_L1D_Logged.lift (core.result.Result.map_err
              (prover.prove_masked_with_attempt.closure_2.Insts.CoreOpsFunctionFnOnceTupleVecQM31Error
              aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r8 ())
          let cf4 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r9)
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let i := alloc.vec.Vec.len val1.g
            if i != 1024#usize
            then
              Pure.pure (core.result.Result.Err verifier.Error.Semantic, nonce_store1)
            else
              let i1 := alloc.vec.Vec.len val1.h1_padding
              if i1 != 1024#usize
              then
                Pure.pure (core.result.Result.Err verifier.Error.Semantic,
                  nonce_store1)
              else
                let s := alloc.vec.Vec.deref val1.g
                let g ← PV_L1D_Logged.lift (prover.fixed_k_column s)
                let s1 := alloc.vec.Vec.deref val1.h1_padding
                let h1_padding ← PV_L1D_Logged.lift (prover.fixed_k_column s1)
                let s2 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice noised_c11.c1))
                let audit ←
                  PV_L1D_Source_037.produce s2 val1.mask_only_c1 val4 g h1_padding
                    val2
                if audit.c1_columns_inactive_balanced != 16#usize
                then
                  Pure.pure (core.result.Result.Err verifier.Error.Semantic,
                    nonce_store1)
                else
                  if audit.mask_only_columns_inactive_balanced != 10#usize
                  then
                    Pure.pure (core.result.Result.Err verifier.Error.Semantic,
                      nonce_store1)
                  else
                    if audit.d_inactive_balanced
                    then
                      if audit.g_inactive_balanced
                      then
                        if audit.h1_padding_inactive_balanced
                        then
                          let i2 ← PV_L1D_Logged.lift (aspis_core.r0.merkle.C1_TAG)
                          let r10 ←
                            PV_L1D_Source_030.produce reserved context hash
                              i2
                          let cf5 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r10)
                          match cf5 with
                          | core.ops.control_flow.ControlFlow.Continue val5 =>
                            let i3 ← PV_L1D_Logged.lift (aspis_core.r0.merkle.C2_TAG)
                            let r11 ←
                              PV_L1D_Source_030.produce reserved context hash
                                i3
                            let cf6 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r11)
                            match cf6 with
                            | core.ops.control_flow.ControlFlow.Continue val6
                              =>
                              let r12 ← PV_L1D_Logged.lift (host_commitment.EncodingDomain.new)
                              let r13 ← PV_L1D_Logged.lift (core.result.Result.map_err
                                  (prover.prove_masked_with_attempt.closure_3.Insts.CoreOpsFunctionFnOnceTupleErrorError
                                  aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst)
                                  r12 ())
                              let cf7 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r13)
                              match cf7 with
                              | core.ops.control_flow.ControlFlow.Continue val7
                                =>
                                let we ← PV_L1D_Logged.lift (aspis_core.field.wide_exact.WideExact.ZERO)
                                let a := Array.repeat 1024#usize we
                                let v ← PV_L1D_Logged.lift (alloc.vec.from_elem (core.clone.CloneArray
                                    1024#usize
                                    aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone)
                                    a 29#usize)
                                let (r14, backend) ←
                                  PV_L1D_Source_068.produce
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
                                let r15 ← PV_L1D_Logged.lift (core.result.Result.map_err (BuiltinFnOnce
                                    r1_wire.Error verifier.Error) r14
                                    (prover.semantic_error))
                                let cf8 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch
                                    r15)
                                match cf8 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val8 =>
                                  let v1 ← PV_L1D_Logged.lift (Array.index_usize val8.columns 26#usize)
                                  let s3 := alloc.vec.Vec.deref v1
                                  let o ← PV_L1D_Logged.lift (aspis_statement.state_only_semantic.state_only_copy_helper_sum
                                      s3)
                                  let q ← PV_L1D_Logged.lift (aspis_core.field.QM31.ZERO)
                                  let h1_total_balanced ← PV_L1D_Logged.lift (core.option.Option.Insts.CoreCmpPartialEqOption.eq
                                      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                      o (some q))
                                  if h1_total_balanced
                                  then
                                    let r16 ←
                                      PV_L1D_Source_031.produce public1
                                        variant hash backend val8 (reserved,
                                        context)
                                    let cf9 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch
                                        r16)
                                    match cf9 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val9 =>
                                      Pure.pure (core.result.Result.Ok (val9,
                                        { audit with h1_total_balanced := true
                                        }), nonce_store1)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      let r17 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          ((alloc.vec.Vec Std.U8) ×
                                          prover.MaskedFixtureAudit)
                                          (core.convert.FromSame
                                          verifier.Error) residual)
                                      Pure.pure (r17, nonce_store1)
                                  else
                                    Pure.pure (core.result.Result.Err
                                      verifier.Error.Semantic, nonce_store1)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  let r16 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      ((alloc.vec.Vec Std.U8) ×
                                      prover.MaskedFixtureAudit)
                                      (core.convert.FromSame verifier.Error)
                                      residual)
                                  Pure.pure (r16, nonce_store1)
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                let r14 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    ((alloc.vec.Vec Std.U8) ×
                                    prover.MaskedFixtureAudit)
                                    (core.convert.FromSame verifier.Error)
                                    residual)
                                Pure.pure (r14, nonce_store1)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              let r12 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  ((alloc.vec.Vec Std.U8) ×
                                  prover.MaskedFixtureAudit)
                                  (core.convert.FromSame verifier.Error)
                                  residual)
                              Pure.pure (r12, nonce_store1)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r11 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                ((alloc.vec.Vec Std.U8) ×
                                prover.MaskedFixtureAudit)
                                (core.convert.FromSame verifier.Error) residual)
                            Pure.pure (r11, nonce_store1)
                        else
                          Pure.pure (core.result.Result.Err verifier.Error.Semantic,
                            nonce_store1)
                      else
                        Pure.pure (core.result.Result.Err verifier.Error.Semantic,
                          nonce_store1)
                    else
                      Pure.pure (core.result.Result.Err verifier.Error.Semantic,
                        nonce_store1)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r10 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
                (core.convert.FromSame verifier.Error) residual)
            Pure.pure (r10, nonce_store1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r8 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
              (core.convert.FromSame verifier.Error) residual)
          Pure.pure (r8, nonce_store1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r6 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
            (core.convert.FromSame verifier.Error) residual)
        Pure.pure (r6, nonce_store1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r4 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
          (core.convert.FromSame verifier.Error) residual)
      Pure.pure (r4, nonce_store1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual)
    Pure.pure (r2, nonce_store1)

theorem complete_result
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
  erase (produce (T0 := T0) aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash context binding attempt nonce_store) = prover.prove_masked_with_attempt (T0 := T0) aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash context binding attempt nonce_store := by
  unfold produce
  conv_rhs => unfold prover.prove_masked_with_attempt
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_030.complete_result,PV_L1D_Source_031.complete_result,PV_L1D_Source_037.complete_result,PV_L1D_Source_068.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_030.complete_result,PV_L1D_Source_031.complete_result,PV_L1D_Source_037.complete_result,PV_L1D_Source_068.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_030.complete_result,PV_L1D_Source_031.complete_result,PV_L1D_Source_037.complete_result,PV_L1D_Source_068.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_069
