import R1Z.PV_RunJoin_NativeAfterBuild55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeAfterAudit55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
variable [ExternalTypes] [ExternalFuns]
def run {A T0 : Type} (publish : Phase → Result (core.result.Result A verifier.Error))
    (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (variant : transport.Variant) (hash : aspis_core.digest.LegacyHashFn)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g h1_padding : Array aspis_core.field.QM31 1024#usize)
    (audit : prover.MaskedFixtureAudit) (store : T0) :
    Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T0) := do
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
            public1 compiled noised
            maskOnly d g h1_padding
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
        PV_RunJoin_NativeAfterBuild55.run publish public1 variant hash backend reserved context audit store r14
      | core.ops.control_flow.ControlFlow.Break
        residual =>
        let r14 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (A × prover.MaskedFixtureAudit)
            (core.convert.FromSame verifier.Error)
            residual
        ok (r14, store)
    | core.ops.control_flow.ControlFlow.Break residual
      =>
      let r12 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (A × prover.MaskedFixtureAudit)
          (core.convert.FromSame verifier.Error)
          residual
      ok (r12, store)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r11 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (A × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual
    ok (r11, store)
#print axioms run
end R1Z.PV_RunJoin_NativeAfterAudit55
