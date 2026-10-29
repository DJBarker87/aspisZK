import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_041
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F)
  (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8)
  (point : Array aspis_core.field.QM31 10#usize)
  (running : aspis_core.field.QM31) (round : Std.Usize) (oracle : F) :
  Logged ((core.result.Result ((Array aspis_core.field.QM31 10#usize) ×
    aspis_core.field.QM31) r1_wire.Error) × (host_wire.SemanticTranscript H)
    × (alloc.vec.Vec Std.U8))
  := do
  let _ ← observe (.boundary 0) 0 (ok ())
  let remaining ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_sub 9#usize round))
  let _ ← PV_L1D_Logged.lift (aspis_core.field.QM31.ZERO)
  let assignments ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_shl 1#usize (UScalar.cast .U32 remaining)))
  let i ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add 100#usize round))
  let i1 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_mul 28#usize assignments))
  let evaluations ← PV_L1D_Logged.lift (host_work.map
      (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error
      aspis_coredigestDigest32Inst OracleInst) i i1 (oracle, point, round,
      assignments))
  let s := alloc.vec.Vec.deref evaluations
  let r ← PV_L1D_Logged.lift (host_sumcheck.merge_evaluations s assignments)
  let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let polynomial ← PV_L1D_Logged.lift (host_sumcheck.interpolate val)
    let q ← PV_L1D_Logged.lift (aspis_core.state_only_sumcheck.state_only_boundary_sum polynomial)
    let b ← PV_L1D_Logged.lift (core.cmp.PartialEq.ne.trait_default
        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q running)
    if b
    then
      Pure.pure (core.result.Result.Err (r1_wire.Error.Boundary round), transcript,
        output)
    else
      let polynomial_bytes ← PV_L1D_Logged.lift (host_sumcheck.encode_polynomial polynomial)
      let i2 ← PV_L1D_Logged.lift (Aeneas.Std.lift (UScalar.cast .U8 round))
      let i3 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.U8.wrapping_add 15#u8 i2))
      let s1 := alloc.vec.Vec.deref polynomial_bytes
      let r1 ← PV_L1D_Logged.lift (host_wire.record i3 s1)
      let cf1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let i4 ← PV_L1D_Logged.lift (Aeneas.Std.lift (UScalar.cast .U8 round))
        let i5 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.U8.wrapping_add 15#u8 i4))
        let s2 := alloc.vec.Vec.deref val1
        let (r2, transcript1) ← PV_L1D_Logged.lift (host_wire.SemanticTranscript.semantic aspis_coredigestDigest32Inst
            transcript i5 s2)
        let cf2 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let point1 ← PV_L1D_Logged.lift (Array.update point round val2)
          let s3 := alloc.vec.Vec.deref val1
          let output1 ← PV_L1D_Logged.lift (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 output s3)
          let q1 ← PV_L1D_Logged.lift (Array.index_usize point1 round)
          let running1 ← PV_L1D_Logged.lift (aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
              polynomial q1)
          Pure.pure (core.result.Result.Ok (point1, running1), transcript1, output1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
              (core.convert.FromSame r1_wire.Error) residual)
          Pure.pure (r3, transcript1, output)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
            (core.convert.FromSame r1_wire.Error) residual)
        Pure.pure (r2, transcript, output)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
        (core.convert.FromSame r1_wire.Error) residual)
    Pure.pure (r1, transcript, output)

theorem complete_result
  {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F)
  (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8)
  (point : Array aspis_core.field.QM31 10#usize)
  (running : aspis_core.field.QM31) (round : Std.Usize) (oracle : F) :
  erase (produce (H := H) (F := F) aspis_coredigestDigest32Inst OracleInst transcript output point running round oracle) = host_sumcheck.prove_sumcheck_round (H := H) (F := F) aspis_coredigestDigest32Inst OracleInst transcript output point running round oracle := by
  unfold produce
  conv_rhs => unfold host_sumcheck.prove_sumcheck_round
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_041
