import R1Z.PV_RunJoin_PrepareOperations47
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareClaimContext48
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def run
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (coefficient_result : Result (alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize)))
  (constructor : Result (core.result.Result weights.Weights verifier.Error))
  (materialize : weights.Weights → aspis_core.field.wide_exact.WideExact →
    Result (core.result.Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) verifier.Error))
  (claim : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize) →
    aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact → Result (alloc.vec.Vec U8))
  (inactiveValue : Slice aspis_core.field.wide_exact.WideExact → weights.Weights →
    Result aspis_core.field.wide_exact.WideExact) :
  Result (core.result.Result prover.PreparedOpening verifier.Error)
  := do
  let b ←
    core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant variant
      transport.Variant.S2
  if b
  then ok (core.result.Result.Err verifier.Error.Semantic)
  else
    let s := alloc.vec.Vec.deref backend.messages
    let coefficients ← coefficient_result
    let scp ← Array.index_usize sem.z 1#usize
    let we ← aspis_core.field.wide_exact.WideExact.from_qm31 scp.x
    let we1 ← aspis_core.field.wide_exact.WideExact.from_qm31 scp.y
    let s1 := alloc.vec.Vec.deref coefficients
    let y1 ← claim s1 { x := we, y := we1 }
    let a ←
      host_wire.SemanticTranscript.impl.state
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        sem.transcript
    let transcript ←
      host_transcript.Transcript.new
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 hash a
        variant
    let s2 := alloc.vec.Vec.deref y1
    let (gamma, transcript1) ←
      host_transcript.Transcript.scalar
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        transcript 27#u8 s2 true
    let s3 := alloc.vec.Vec.deref coefficients
    let q ← prover.opening_batch s3 gamma
    let r ← constructor
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s4 := alloc.vec.Vec.deref q
      let inactive ← inactiveValue s4 val
      let a1 ← aspis_core.field.wide_exact.WideExact.to_le_bytes inactive
      let s5 ← Aeneas.Std.lift (Array.to_slice a1)
      let (kappa, transcript2) ←
        host_transcript.Transcript.scalar
          aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
          transcript1 28#u8 s5 false
      let r1 ← materialize val kappa
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s6 := alloc.vec.Vec.deref q
        let s7 := alloc.vec.Vec.deref val1
        let c0 ← prover.round s6 s7
        let s8 ← Aeneas.Std.lift (Array.to_slice c0)
        let c0bytes ← prover.encoded_slice s8
        let s9 := alloc.vec.Vec.deref c0bytes
        let (alpha0, transcript3) ←
          host_transcript.Transcript.scalar
            aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
            transcript2 29#u8 s9 false
        let s10 := alloc.vec.Vec.deref q
        let q1 ← prover.fold s10 alpha0 false
        let s11 := alloc.vec.Vec.deref val1
        let w1 ← prover.fold s11 alpha0 true
        let s12 := alloc.vec.Vec.deref q1
        let r2 ←
          host_commitment.EncodingDomain.evaluate
            aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
            backend.domain s12 0#usize
        let r3 ←
          core.result.Result.map_err
            prover.prepare_opening.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
            r2 ()
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          ok (core.result.Result.Ok
            {
              backend,
              sem,
              transcript := transcript3,
              y1,
              gamma,
              inactive,
              kappa,
              alpha0,
              c0bytes,
              q1,
              w1,
              folded_word := val2
            })
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            prover.PreparedOpening (core.convert.FromSame verifier.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.PreparedOpening (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        prover.PreparedOpening (core.convert.FromSame verifier.Error) residual


theorem source (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (backend : prover.Backend)
    (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (coefficients : Result (alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize)))
    (constructor : Result (core.result.Result weights.Weights verifier.Error))
    (materialize : weights.Weights → aspis_core.field.wide_exact.WideExact →
      Result (core.result.Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) verifier.Error)) :
    PV_RunJoin_PrepareOperations47.run variant hash backend sem coefficients constructor materialize=
      run variant hash backend sem coefficients constructor materialize
        prover.opening_claim_bytes prover.opening_inactive := by rfl
#print axioms source
end R1Z.PV_RunJoin_PrepareClaimContext48
