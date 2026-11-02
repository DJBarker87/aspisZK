import R1Z.PV_RunJoin_RoundWorkerReached69
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RoundAfterPolynomial72
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Q := aspis_core.field.QM31

def run {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (running : Q) (round : Usize)
    (polynomial : Array Q 28#usize) :
    Result (core.result.Result (Array Q 10#usize × Q) r1_wire.Error ×
      host_wire.SemanticTranscript H × alloc.vec.Vec U8) := do
  let q ← aspis_core.state_only_sumcheck.state_only_boundary_sum polynomial
  let b ←
    core.cmp.PartialEq.ne.trait_default
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q running
  if b
  then
    ok (core.result.Result.Err (r1_wire.Error.Boundary round), transcript,
      output)
  else
    let polynomial_bytes ← host_sumcheck.encode_polynomial polynomial
    let i2 ← Aeneas.Std.lift (UScalar.cast .U8 round)
    let i3 ← Aeneas.Std.lift (Std.U8.wrapping_add 15#u8 i2)
    let s1 := alloc.vec.Vec.deref polynomial_bytes
    let r1 ← host_wire.record i3 s1
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let i4 ← Aeneas.Std.lift (UScalar.cast .U8 round)
      let i5 ← Aeneas.Std.lift (Std.U8.wrapping_add 15#u8 i4)
      let s2 := alloc.vec.Vec.deref val1
      let (r2, transcript1) ←
        host_wire.SemanticTranscript.semantic aspis_coredigestDigest32Inst
          transcript i5 s2
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let point1 ← Array.update point round val2
        let s3 := alloc.vec.Vec.deref val1
        let output1 ←
          alloc.vec.Vec.extend_from_slice core.clone.CloneU8 output s3
        let q1 ← Array.index_usize point1 round
        let running1 ←
          aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
            polynomial q1
        ok (core.result.Result.Ok (point1, running1), transcript1, output1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
            (core.convert.FromSame r1_wire.Error) residual
        ok (r3, transcript1, output)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
          (core.convert.FromSame r1_wire.Error) residual
      ok (r2, transcript, output)

theorem reached {H : Type} (digest : aspis_core.digest.Digest32 H)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (running : Q) (round assignments : Usize)
    (evaluations : PV_RunJoin_RoundWorkerReached69.Evaluations)
    (values polynomial : Array Q 28#usize)
    (merged : host_sumcheck.merge_evaluations (alloc.vec.Vec.deref evaluations) assignments=ok (.Ok values))
    (interpolated : host_sumcheck.interpolate values=ok polynomial) :
    PV_RunJoin_RoundWorkerReached69.tail digest transcript output point running round assignments evaluations=
      run digest transcript output point running round polynomial := by
  simp only [PV_RunJoin_RoundWorkerReached69.tail,merged,interpolated,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,run]

#print axioms run
#print axioms reached
end R1Z.PV_RunJoin_RoundAfterPolynomial72
