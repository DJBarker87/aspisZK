import R1Z.PV_RunJoin_NativeControl55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeAfterBuild55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
variable [ExternalTypes] [ExternalFuns]
def run {A T : Type} (publish : Phase → Result (core.result.Result A verifier.Error))
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (variant : transport.Variant) (hash : aspis_core.digest.LegacyHashFn)
    (backend : prover.Backend)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (audit : prover.MaskedFixtureAudit) (store : T)
    (r14 : core.result.Result (host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) r1_wire.Error) :
    Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T) := do
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
        publish ⟨public1,variant,hash,backend,val8,(reserved,context)⟩
      let cf9 ←
        core.result.Result.Insts.CoreOpsTry.branch
          r16
      match cf9 with
      |
        core.ops.control_flow.ControlFlow.Continue
        val9 =>
        ok (core.result.Result.Ok (val9,
          { audit with h1_total_balanced := true
          }), store)
      | core.ops.control_flow.ControlFlow.Break
        residual =>
        let r17 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (A × prover.MaskedFixtureAudit)
            (core.convert.FromSame
            verifier.Error) residual
        ok (r17, store)
    else
      ok (core.result.Result.Err
        verifier.Error.Semantic, store)
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    let r16 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (A × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error)
        residual
    ok (r16, store)
#print axioms run
end R1Z.PV_RunJoin_NativeAfterBuild55
