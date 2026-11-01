import PV_EVH_DurableReserveBuild
import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_DurableWithAttempt
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  op231_OPEN : ∀ (arg0 : aspis_statement.state_only_trace.StateOnlyTraceFoundation), P (aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  apply_pool_v1_pair_forest_mask_material_v1_OPEN : ∀ (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial), P (((core.result.Result
    aspis_prover.state_only_hiding.AppliedStateOnlyMasks
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation))
  op134_OPEN : P ((core.result.Result (Array Std.U16 64#usize) aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1))
  derive_pool_v1_pair_forest_zero_factor_d_OPEN : ∀ (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext), P ((core.result.Result (alloc.vec.Vec aspis_core.field.QM31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError))
  op36_OPEN : ∀ {T : Type} (A : Type) (N : Std.Usize) (arg0 : (alloc.vec.Vec T)), P ((core.result.Result (Array T N) (alloc.vec.Vec T)))
  fixed_k_column_OPEN : ∀ (values : Slice aspis_core.field.QM31), P ((Array aspis_core.field.QM31 1024#usize))
  audit_masks_OPEN : ∀ (c1 : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize)
  (masks : Array Std.U16 64#usize), P (prover.MaskedFixtureAudit)
  op82_OPEN : P (Std.U8)
  derive_private_salts_OPEN : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8), P ((core.result.Result host_commitment.PrivateSalts verifier.Error))
  op83_OPEN : P (Std.U8)
  new_OPEN : P ((core.result.Result host_commitment.EncodingDomain
    aspis_core.r0.Error))
  op42_OPEN : P (aspis_core.field.wide_exact.WideExact)
  fromElem_OPEN : ∀ {T : Type} (inst : core.clone.Clone T) (value : T) (count : Usize), P (alloc.vec.Vec T)
  build_with_material_OPEN : ∀ {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (CommitmentsInst : host_semantic.Commitments
  T1)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (noised_semantic_c1 :
  aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize) (commitments : T1)
  (hash : H) (variant : transport.Variant), P (((core.result.Result (host_semantic.BuiltSemantics H) r1_wire.Error)
    × T1))
  op230_OPEN : ∀ (arg0 : (Slice aspis_core.field.QM31)), P ((Option aspis_core.field.QM31))
  op64_OPEN : P (aspis_core.field.QM31)
  op8_OPEN : ∀ {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (arg0 : (Option T)) (arg1 : (Option T)), P (Bool)
  prove_from_semantics_OPEN : ∀ (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_core.state_only_hiding.StateOnlyHidingContext)), P ((core.result.Result (alloc.vec.Vec Std.U8) verifier.Error))

structure Compatible (c : Callees) : Prop where
  op231_fixed : ∀ (arg0 : aspis_statement.state_only_trace.StateOnlyTraceFoundation), FinishedView (c.op231_OPEN arg0) (aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone arg0)
  apply_pool_v1_pair_forest_mask_material_v1_fixed : ∀ (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial), FinishedView (c.apply_pool_v1_pair_forest_mask_material_v1_OPEN trace material) (aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 trace material)
  op134_fixed : FinishedView (c.op134_OPEN) (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1)
  derive_pool_v1_pair_forest_zero_factor_d_fixed : ∀ (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext), FinishedView (c.derive_pool_v1_pair_forest_zero_factor_d_OPEN self hash context) (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d self hash context)
  op36_fixed : ∀ {T : Type} (A : Type) (N : Std.Usize) (arg0 : (alloc.vec.Vec T)), FinishedView (c.op36_OPEN A N arg0) (Array.Insts.CoreConvertTryFromVecVec.try_from A N arg0)
  fixed_k_column_fixed : ∀ (values : Slice aspis_core.field.QM31), FinishedView (c.fixed_k_column_OPEN values) (prover.fixed_k_column values)
  audit_masks_fixed : ∀ (c1 : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize)
  (masks : Array Std.U16 64#usize), FinishedView (c.audit_masks_OPEN c1 mask_only d g h1_padding masks) (prover.audit_masks c1 mask_only d g h1_padding masks)
  op82_fixed : FinishedView (c.op82_OPEN) (aspis_core.r0.merkle.C1_TAG)
  derive_private_salts_fixed : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8), FinishedView (c.derive_private_salts_OPEN reserved context hash tag) (prover.derive_private_salts reserved context hash tag)
  op83_fixed : FinishedView (c.op83_OPEN) (aspis_core.r0.merkle.C2_TAG)
  new_fixed : FinishedView (c.new_OPEN) (host_commitment.EncodingDomain.new)
  op42_fixed : FinishedView (c.op42_OPEN) (aspis_core.field.wide_exact.WideExact.ZERO)
  fromElem_fixed : ∀ {T : Type} (inst : core.clone.Clone T) (value : T) (count : Usize), FinishedView (c.fromElem_OPEN inst value count) (alloc.vec.from_elem inst value count)
  build_with_material_fixed : ∀ {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (CommitmentsInst : host_semantic.Commitments
  T1)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (noised_semantic_c1 :
  aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize) (commitments : T1)
  (hash : H) (variant : transport.Variant), FinishedView (c.build_with_material_OPEN aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant) (host_semantic.build_with_material aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant)
  op230_fixed : ∀ (arg0 : (Slice aspis_core.field.QM31)), FinishedView (c.op230_OPEN arg0) (aspis_statement.state_only_semantic.state_only_copy_helper_sum arg0)
  op64_fixed : FinishedView (c.op64_OPEN) (aspis_core.field.QM31.ZERO)
  op8_fixed : ∀ {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (arg0 : (Option T)) (arg1 : (Option T)), FinishedView (c.op8_OPEN cmpPartialEqInst arg0 arg1) (core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst arg0 arg1)
  prove_from_semantics_fixed : ∀ (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_core.state_only_hiding.StateOnlyHidingContext)), FinishedView (c.prove_from_semantics_OPEN public1 variant hash backend sem salts) (prover.prove_from_semantics public1 variant hash backend sem salts)

def run
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (binding : Array Std.U8 32#usize)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (fileAnswers : PV_EVH_NonceWorld.Answers) (reserveCallees : PV_EVH_DurableReserveBuild.Callees) (c : Callees) : P ((core.result.Result ((alloc.vec.Vec Std.U8) ×
    prover.MaskedFixtureAudit) verifier.Error) × aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let (r, nonce_store1) ← PV_EVH_DurableReserveBuild.run attempt hash binding context nonce_store fileAnswers reserveCallees
  let r1 ← PV_EVH_Prefix.lift (core.result.Result.map_err (BuiltinFnOnce
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError verifier.Error) r
      (prover.mask_error))
  let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (reserved, material) := val
    let noised_c1 ← c.op231_OPEN
        compiled.semantic_c1
    let (r2, noised_c11) ← c.apply_pool_v1_pair_forest_mask_material_v1_OPEN
        noised_c1 material
    let r3 ← PV_EVH_Prefix.lift (core.result.Result.map_err
        (prover.prove_masked_with_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
        aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r2 ())
    let cf1 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r3)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r4 ← c.op134_OPEN
      let r5 ← PV_EVH_Prefix.lift (core.result.Result.map_err
          (prover.prove_masked_with_attempt.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error
          aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r4 ())
      let cf2 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r5)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r6 ← c.derive_pool_v1_pair_forest_zero_factor_d_OPEN
            reserved hash context
        let r7 ← PV_EVH_Prefix.lift (core.result.Result.map_err (BuiltinFnOnce
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError
            verifier.Error) r6 (prover.mask_error))
        let cf3 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r7)
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r8 ← c.op36_OPEN Global 1024#usize
              val3
          let r9 ← PV_EVH_Prefix.lift (core.result.Result.map_err
              (prover.prove_masked_with_attempt.closure_2.Insts.CoreOpsFunctionFnOnceTupleVecQM31Error
              aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r8 ())
          let cf4 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r9)
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
                let g ← c.fixed_k_column_OPEN s
                let s1 := alloc.vec.Vec.deref val1.h1_padding
                let h1_padding ← c.fixed_k_column_OPEN s1
                let s2 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice noised_c11.c1))
                let audit ← c.audit_masks_OPEN s2 val1.mask_only_c1 val4 g h1_padding
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
                          let i2 ← c.op82_OPEN
                          let r10 ← c.derive_private_salts_OPEN reserved context hash
                              i2
                          let cf5 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r10)
                          match cf5 with
                          | core.ops.control_flow.ControlFlow.Continue val5 =>
                            let i3 ← c.op83_OPEN
                            let r11 ← c.derive_private_salts_OPEN reserved context hash
                                i3
                            let cf6 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r11)
                            match cf6 with
                            | core.ops.control_flow.ControlFlow.Continue val6 =>
                              let r12 ← c.new_OPEN
                              let r13 ← PV_EVH_Prefix.lift (core.result.Result.map_err
                                  (prover.prove_masked_with_attempt.closure_3.Insts.CoreOpsFunctionFnOnceTupleErrorError
                                  aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst)
                                  r12 ())
                              let cf7 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r13)
                              match cf7 with
                              | core.ops.control_flow.ControlFlow.Continue val7 =>
                                let we ← c.op42_OPEN
                                let a := Array.repeat 1024#usize we
                                let v ← c.fromElem_OPEN (core.clone.CloneArray
                                    1024#usize
                                    aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone)
                                    a 29#usize
                                let (r14, backend) ← c.build_with_material_OPEN
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
                                let r15 ← PV_EVH_Prefix.lift (core.result.Result.map_err (BuiltinFnOnce
                                    r1_wire.Error verifier.Error) r14
                                    (prover.semantic_error))
                                let cf8 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch
                                    r15)
                                match cf8 with
                                | core.ops.control_flow.ControlFlow.Continue val8 =>
                                  let v1 ← PV_EVH_Prefix.lift (Array.index_usize val8.columns 26#usize)
                                  let s3 := alloc.vec.Vec.deref v1
                                  let o ← c.op230_OPEN
                                      s3
                                  let q ← c.op64_OPEN
                                  let h1_total_balanced ← c.op8_OPEN
                                      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                      o (some q)
                                  if h1_total_balanced then
                                    let r16 ← c.prove_from_semantics_OPEN public1
                                        variant hash backend val8 (reserved,
                                        context)
                                    let cf9 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch
                                        r16)
                                    match cf9 with
                                    | core.ops.control_flow.ControlFlow.Continue val9 =>
                                      pure (core.result.Result.Ok (val9,
                                        { audit with h1_total_balanced := true
                                        }), nonce_store1)
                                    | core.ops.control_flow.ControlFlow.Break residual =>
                                      let r17 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          ((alloc.vec.Vec Std.U8) ×
                                          prover.MaskedFixtureAudit)
                                          (core.convert.FromSame
                                          verifier.Error) residual)
                                      pure (r17, nonce_store1)
                                  else
                                    pure (core.result.Result.Err
                                      verifier.Error.Semantic, nonce_store1)
                                | core.ops.control_flow.ControlFlow.Break residual =>
                                  let r16 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      ((alloc.vec.Vec Std.U8) ×
                                      prover.MaskedFixtureAudit)
                                      (core.convert.FromSame verifier.Error)
                                      residual)
                                  pure (r16, nonce_store1)
                              | core.ops.control_flow.ControlFlow.Break residual =>
                                let r14 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    ((alloc.vec.Vec Std.U8) ×
                                    prover.MaskedFixtureAudit)
                                    (core.convert.FromSame verifier.Error)
                                    residual)
                                pure (r14, nonce_store1)
                            | core.ops.control_flow.ControlFlow.Break residual =>
                              let r12 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  ((alloc.vec.Vec Std.U8) ×
                                  prover.MaskedFixtureAudit)
                                  (core.convert.FromSame verifier.Error)
                                  residual)
                              pure (r12, nonce_store1)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r11 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
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
            let r10 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
                (core.convert.FromSame verifier.Error) residual)
            pure (r10, nonce_store1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r8 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
              (core.convert.FromSame verifier.Error) residual)
          pure (r8, nonce_store1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r6 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
            (core.convert.FromSame verifier.Error) residual)
        pure (r6, nonce_store1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r4 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
          (core.convert.FromSame verifier.Error) residual)
      pure (r4, nonce_store1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual)
    pure (r2, nonce_store1)

theorem run_fixed
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (binding : Array Std.U8 32#usize)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (fileAnswers : PV_EVH_NonceWorld.Answers) (reserveCallees : PV_EVH_DurableReserveBuild.Callees) (c : Callees) (compatible : Compatible c) (files_same : PV_EVH_NonceWorld.Compatible fileAnswers) (reserve_same : PV_EVH_DurableReserveBuild.Compatible reserveCallees) :
    FinishedView (run public1 compiled variant hash context binding attempt nonce_store fileAnswers reserveCallees c) (prover.prove_masked_with_attempt aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore public1 compiled variant hash context binding attempt nonce_store) := by
  unfold run prover.prove_masked_with_attempt
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact PV_EVH_DurableReserveBuild.run_fixed _ _ _ _ _ fileAnswers reserveCallees reserve_same files_same
  · rintro ⟨r, nonce_store1⟩
    try dsimp only
    apply PV_EVH_Prefix.bind_fixed
    ·
      exact PV_EVH_Prefix.lift_fixed _
    · intro r1
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact PV_EVH_Prefix.lift_fixed _
      · intro cf
        try dsimp only
        cases cf with
        | Continue val =>
          let (reserved, material) := val
          try dsimp only
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact compatible.op231_fixed _
          · intro noised_c1
            try dsimp only
            apply PV_EVH_Prefix.bind_fixed
            ·
              exact compatible.apply_pool_v1_pair_forest_mask_material_v1_fixed _ _
            · rintro ⟨r2, noised_c11⟩
              try dsimp only
              apply PV_EVH_Prefix.bind_fixed
              ·
                exact PV_EVH_Prefix.lift_fixed _
              · intro r3
                try dsimp only
                apply PV_EVH_Prefix.bind_fixed
                ·
                  exact PV_EVH_Prefix.lift_fixed _
                · intro cf1
                  try dsimp only
                  cases cf1 with
                  | Continue val1 =>
                    try dsimp only
                    apply PV_EVH_Prefix.bind_fixed
                    ·
                      exact compatible.op134_fixed
                    · intro r4
                      try dsimp only
                      apply PV_EVH_Prefix.bind_fixed
                      ·
                        exact PV_EVH_Prefix.lift_fixed _
                      · intro r5
                        try dsimp only
                        apply PV_EVH_Prefix.bind_fixed
                        ·
                          exact PV_EVH_Prefix.lift_fixed _
                        · intro cf2
                          try dsimp only
                          cases cf2 with
                          | Continue val2 =>
                            try dsimp only
                            apply PV_EVH_Prefix.bind_fixed
                            ·
                              exact compatible.derive_pool_v1_pair_forest_zero_factor_d_fixed _ _ _
                            · intro r6
                              try dsimp only
                              apply PV_EVH_Prefix.bind_fixed
                              ·
                                exact PV_EVH_Prefix.lift_fixed _
                              · intro r7
                                try dsimp only
                                apply PV_EVH_Prefix.bind_fixed
                                ·
                                  exact PV_EVH_Prefix.lift_fixed _
                                · intro cf3
                                  try dsimp only
                                  cases cf3 with
                                  | Continue val3 =>
                                    try dsimp only
                                    apply PV_EVH_Prefix.bind_fixed
                                    ·
                                      exact compatible.op36_fixed _ _ _
                                    · intro r8
                                      try dsimp only
                                      apply PV_EVH_Prefix.bind_fixed
                                      ·
                                        exact PV_EVH_Prefix.lift_fixed _
                                      · intro r9
                                        try dsimp only
                                        apply PV_EVH_Prefix.bind_fixed
                                        ·
                                          exact PV_EVH_Prefix.lift_fixed _
                                        · intro cf4
                                          try dsimp only
                                          cases cf4 with
                                          | Continue val4 =>
                                            let i := alloc.vec.Vec.len val1.g
                                            try dsimp only
                                            by_cases condition : i != 1024#usize
                                            · try dsimp only [i] at condition
                                              simp only [condition,if_true]
                                              exact PV_EVH_Prefix.lift_fixed _
                                            · try dsimp only [i] at condition
                                              simp only [condition,if_false]
                                              let i1 := alloc.vec.Vec.len val1.h1_padding
                                              try dsimp only
                                              by_cases condition : i1 != 1024#usize
                                              · try dsimp only [i,i1] at condition
                                                simp only [condition,if_true]
                                                exact PV_EVH_Prefix.lift_fixed _
                                              · try dsimp only [i,i1] at condition
                                                simp only [condition,if_false]
                                                let s := alloc.vec.Vec.deref val1.g
                                                try dsimp only
                                                try dsimp only
                                                apply PV_EVH_Prefix.bind_fixed
                                                ·
                                                  exact compatible.fixed_k_column_fixed _
                                                · intro g
                                                  let s1 := alloc.vec.Vec.deref val1.h1_padding
                                                  try dsimp only
                                                  try dsimp only
                                                  apply PV_EVH_Prefix.bind_fixed
                                                  ·
                                                    exact compatible.fixed_k_column_fixed _
                                                  · intro h1_padding
                                                    try dsimp only
                                                    apply PV_EVH_Prefix.bind_fixed
                                                    ·
                                                      exact PV_EVH_Prefix.lift_fixed _
                                                    · intro s2
                                                      try dsimp only
                                                      apply PV_EVH_Prefix.bind_fixed
                                                      ·
                                                        exact compatible.audit_masks_fixed _ _ _ _ _ _
                                                      · intro audit
                                                        by_cases condition : audit.c1_columns_inactive_balanced != 16#usize
                                                        · try dsimp only [i,i1,s,s1] at condition
                                                          simp only [condition,if_true]
                                                          exact PV_EVH_Prefix.lift_fixed _
                                                        · try dsimp only [i,i1,s,s1] at condition
                                                          simp only [condition,if_false]
                                                          by_cases condition : audit.mask_only_columns_inactive_balanced != 10#usize
                                                          · try dsimp only [i,i1,s,s1] at condition
                                                            simp only [condition,if_true]
                                                            exact PV_EVH_Prefix.lift_fixed _
                                                          · try dsimp only [i,i1,s,s1] at condition
                                                            simp only [condition,if_false]
                                                            by_cases condition : audit.d_inactive_balanced
                                                            · try dsimp only [i,i1,s,s1] at condition
                                                              simp only [condition,if_true]
                                                              by_cases condition : audit.g_inactive_balanced
                                                              · try dsimp only [i,i1,s,s1] at condition
                                                                simp only [condition,if_true]
                                                                by_cases condition : audit.h1_padding_inactive_balanced
                                                                · try dsimp only [i,i1,s,s1] at condition
                                                                  simp only [condition,if_true]
                                                                  try dsimp only
                                                                  apply PV_EVH_Prefix.bind_fixed
                                                                  ·
                                                                    exact compatible.op82_fixed
                                                                  · intro i2
                                                                    try dsimp only
                                                                    apply PV_EVH_Prefix.bind_fixed
                                                                    ·
                                                                      exact compatible.derive_private_salts_fixed _ _ _ _
                                                                    · intro r10
                                                                      try dsimp only
                                                                      apply PV_EVH_Prefix.bind_fixed
                                                                      ·
                                                                        exact PV_EVH_Prefix.lift_fixed _
                                                                      · intro cf5
                                                                        try dsimp only
                                                                        cases cf5 with
                                                                        | Continue val5 =>
                                                                          try dsimp only
                                                                          apply PV_EVH_Prefix.bind_fixed
                                                                          ·
                                                                            exact compatible.op83_fixed
                                                                          · intro i3
                                                                            try dsimp only
                                                                            apply PV_EVH_Prefix.bind_fixed
                                                                            ·
                                                                              exact compatible.derive_private_salts_fixed _ _ _ _
                                                                            · intro r11
                                                                              try dsimp only
                                                                              apply PV_EVH_Prefix.bind_fixed
                                                                              ·
                                                                                exact PV_EVH_Prefix.lift_fixed _
                                                                              · intro cf6
                                                                                try dsimp only
                                                                                cases cf6 with
                                                                                | Continue val6 =>
                                                                                  try dsimp only
                                                                                  apply PV_EVH_Prefix.bind_fixed
                                                                                  ·
                                                                                    exact compatible.new_fixed
                                                                                  · intro r12
                                                                                    try dsimp only
                                                                                    apply PV_EVH_Prefix.bind_fixed
                                                                                    ·
                                                                                      exact PV_EVH_Prefix.lift_fixed _
                                                                                    · intro r13
                                                                                      try dsimp only
                                                                                      apply PV_EVH_Prefix.bind_fixed
                                                                                      ·
                                                                                        exact PV_EVH_Prefix.lift_fixed _
                                                                                      · intro cf7
                                                                                        try dsimp only
                                                                                        cases cf7 with
                                                                                        | Continue val7 =>
                                                                                          try dsimp only
                                                                                          apply PV_EVH_Prefix.bind_fixed
                                                                                          ·
                                                                                            exact compatible.op42_fixed
                                                                                          · intro we
                                                                                            let a := Array.repeat 1024#usize we
                                                                                            try dsimp only
                                                                                            try dsimp only
                                                                                            apply PV_EVH_Prefix.bind_fixed
                                                                                            ·
                                                                                              exact compatible.fromElem_fixed _ _ _
                                                                                            · intro v
                                                                                              try dsimp only
                                                                                              apply PV_EVH_Prefix.bind_fixed
                                                                                              ·
                                                                                                exact compatible.build_with_material_fixed _ _ _ _ _ _ _ _ _ _ _ _
                                                                                              · rintro ⟨r14, backend⟩
                                                                                                try dsimp only
                                                                                                apply PV_EVH_Prefix.bind_fixed
                                                                                                ·
                                                                                                  exact PV_EVH_Prefix.lift_fixed _
                                                                                                · intro r15
                                                                                                  try dsimp only
                                                                                                  apply PV_EVH_Prefix.bind_fixed
                                                                                                  ·
                                                                                                    exact PV_EVH_Prefix.lift_fixed _
                                                                                                  · intro cf8
                                                                                                    try dsimp only
                                                                                                    cases cf8 with
                                                                                                    | Continue val8 =>
                                                                                                      try dsimp only
                                                                                                      apply PV_EVH_Prefix.bind_fixed
                                                                                                      ·
                                                                                                        exact PV_EVH_Prefix.lift_fixed _
                                                                                                      · intro v1
                                                                                                        let s3 := alloc.vec.Vec.deref v1
                                                                                                        try dsimp only
                                                                                                        try dsimp only
                                                                                                        apply PV_EVH_Prefix.bind_fixed
                                                                                                        ·
                                                                                                          exact compatible.op230_fixed _
                                                                                                        · intro o
                                                                                                          try dsimp only
                                                                                                          apply PV_EVH_Prefix.bind_fixed
                                                                                                          ·
                                                                                                            exact compatible.op64_fixed
                                                                                                          · intro q
                                                                                                            try dsimp only
                                                                                                            apply PV_EVH_Prefix.bind_fixed
                                                                                                            ·
                                                                                                              exact compatible.op8_fixed _ _ _
                                                                                                            · intro h1_total_balanced
                                                                                                              by_cases condition : h1_total_balanced
                                                                                                              · try dsimp only [i,i1,s,s1,a,s3] at condition
                                                                                                                simp only [condition,if_true]
                                                                                                                try dsimp only
                                                                                                                apply PV_EVH_Prefix.bind_fixed
                                                                                                                ·
                                                                                                                  exact compatible.prove_from_semantics_fixed _ _ _ _ _ _
                                                                                                                · intro r16
                                                                                                                  try dsimp only
                                                                                                                  apply PV_EVH_Prefix.bind_fixed
                                                                                                                  ·
                                                                                                                    exact PV_EVH_Prefix.lift_fixed _
                                                                                                                  · intro cf9
                                                                                                                    try dsimp only
                                                                                                                    cases cf9 with
                                                                                                                    | Continue val9 =>
                                                                                                                      exact PV_EVH_Prefix.lift_fixed _
                                                                                                                    | Break residual =>
                                                                                                                      try dsimp only
                                                                                                                      apply PV_EVH_Prefix.bind_fixed
                                                                                                                      ·
                                                                                                                        exact PV_EVH_Prefix.lift_fixed _
                                                                                                                      · intro r17
                                                                                                                        exact PV_EVH_Prefix.lift_fixed _
                                                                                                              · try dsimp only [i,i1,s,s1,a,s3] at condition
                                                                                                                simp only [condition,if_false]
                                                                                                                exact PV_EVH_Prefix.lift_fixed _
                                                                                                    | Break residual =>
                                                                                                      try dsimp only
                                                                                                      apply PV_EVH_Prefix.bind_fixed
                                                                                                      ·
                                                                                                        exact PV_EVH_Prefix.lift_fixed _
                                                                                                      · intro r16
                                                                                                        exact PV_EVH_Prefix.lift_fixed _
                                                                                        | Break residual =>
                                                                                          try dsimp only
                                                                                          apply PV_EVH_Prefix.bind_fixed
                                                                                          ·
                                                                                            exact PV_EVH_Prefix.lift_fixed _
                                                                                          · intro r14
                                                                                            exact PV_EVH_Prefix.lift_fixed _
                                                                                | Break residual =>
                                                                                  try dsimp only
                                                                                  apply PV_EVH_Prefix.bind_fixed
                                                                                  ·
                                                                                    exact PV_EVH_Prefix.lift_fixed _
                                                                                  · intro r12
                                                                                    exact PV_EVH_Prefix.lift_fixed _
                                                                        | Break residual =>
                                                                          try dsimp only
                                                                          apply PV_EVH_Prefix.bind_fixed
                                                                          ·
                                                                            exact PV_EVH_Prefix.lift_fixed _
                                                                          · intro r11
                                                                            exact PV_EVH_Prefix.lift_fixed _
                                                                · try dsimp only [i,i1,s,s1] at condition
                                                                  simp only [condition,if_false]
                                                                  exact PV_EVH_Prefix.lift_fixed _
                                                              · try dsimp only [i,i1,s,s1] at condition
                                                                simp only [condition,if_false]
                                                                exact PV_EVH_Prefix.lift_fixed _
                                                            · try dsimp only [i,i1,s,s1] at condition
                                                              simp only [condition,if_false]
                                                              exact PV_EVH_Prefix.lift_fixed _
                                          | Break residual =>
                                            try dsimp only
                                            apply PV_EVH_Prefix.bind_fixed
                                            ·
                                              exact PV_EVH_Prefix.lift_fixed _
                                            · intro r10
                                              exact PV_EVH_Prefix.lift_fixed _
                                  | Break residual =>
                                    try dsimp only
                                    apply PV_EVH_Prefix.bind_fixed
                                    ·
                                      exact PV_EVH_Prefix.lift_fixed _
                                    · intro r8
                                      exact PV_EVH_Prefix.lift_fixed _
                          | Break residual =>
                            try dsimp only
                            apply PV_EVH_Prefix.bind_fixed
                            ·
                              exact PV_EVH_Prefix.lift_fixed _
                            · intro r6
                              exact PV_EVH_Prefix.lift_fixed _
                  | Break residual =>
                    try dsimp only
                    apply PV_EVH_Prefix.bind_fixed
                    ·
                      exact PV_EVH_Prefix.lift_fixed _
                    · intro r4
                      exact PV_EVH_Prefix.lift_fixed _
        | Break residual =>
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact PV_EVH_Prefix.lift_fixed _
          · intro r2
            exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_DurableWithAttempt
