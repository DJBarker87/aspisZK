import R1Z.PV_RunJoin_Sequential64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundWorkerReached69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_Sequential64
variable [ExternalTypes] [ExternalFuns]
abbrev Q := aspis_core.field.QM31
abbrev Evaluations := alloc.vec.Vec (core.result.Result Q r1_wire.Error)
/-- Exact source continuation, including length checks, boundary check,
transcript update, array store and all inner errors. -/
def tail {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (running : Q) (round assignments : Usize)
    (evaluations : Evaluations) :
    Result (core.result.Result (Array Q 10#usize × Q) r1_wire.Error ×
      host_wire.SemanticTranscript H × alloc.vec.Vec U8) := do
  let s := alloc.vec.Vec.deref evaluations
  let r ← host_sumcheck.merge_evaluations s assignments
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let polynomial ← host_sumcheck.interpolate val
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
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
        (core.convert.FromSame r1_wire.Error) residual
    ok (r1, transcript, output)

/-- Reached worker count uses the actual round and its remaining assignments.
The closure carries this oracle, point, round and count unchanged. -/
theorem reached {H F : Type} (digest : aspis_core.digest.Digest32 H) (oracleInst : host_sumcheck.Oracle F)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (running : Q) (round : Usize) (oracle : F) :
    host_sumcheck.prove_sumcheck_round digest oracleInst transcript output point running round oracle=
      let assignments := Usize.wrapping_shl 1#usize (UScalar.cast .U32 (Usize.wrapping_sub 9#usize round))
      do let _ ← aspis_core.field.QM31.ZERO
         let evaluations ← host_work.map
           (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error digest oracleInst)
           (Usize.wrapping_add 100#usize round) (Usize.wrapping_mul 28#usize assignments)
           (oracle,point,round,assignments)
         tail digest transcript output point running round assignments evaluations := by
  simp only [host_sumcheck.prove_sumcheck_round,lift,bind_tc_ok]
  rfl

#print axioms tail
#print axioms reached
end R1Z.PV_RunJoin_RoundWorkerReached69
