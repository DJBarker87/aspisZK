import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
import PV_L1_Source_041
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_042
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
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
  if round = 10#usize
  then
    let r ← PV_L1_Logged.lift (OracleInst.evaluate oracle point)
    let cf ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let b ← PV_L1_Logged.lift (core.cmp.PartialEq.ne.trait_default
          aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 val running)
      if b
      then
        Pure.pure (core.result.Result.Err r1_wire.Error.Terminal, transcript, output)
      else Pure.pure (core.result.Result.Ok (point, running), transcript, output)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
          (core.convert.FromSame r1_wire.Error) residual)
      Pure.pure (r1, transcript, output)
  else
    let (r, transcript1, output1) ←
      PV_L1_Source_041.produce aspis_coredigestDigest32Inst
        OracleInst transcript output point running round oracle
    let cf ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (point1, running1) := val
      let i ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add round 1#usize))
      host_sumcheck.prove_sumcheck_rounds aspis_coredigestDigest32Inst
        OracleInst transcript1 output1 point1 running1 i oracle
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
          (core.convert.FromSame r1_wire.Error) residual)
      Pure.pure (r1, transcript1, output1)

theorem complete_result
  {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F)
  (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8)
  (point : Array aspis_core.field.QM31 10#usize)
  (running : aspis_core.field.QM31) (round : Std.Usize) (oracle : F) :
  erase (produce (H := H) (F := F) aspis_coredigestDigest32Inst OracleInst transcript output point running round oracle) = host_sumcheck.prove_sumcheck_rounds (H := H) (F := F) aspis_coredigestDigest32Inst OracleInst transcript output point running round oracle := by
  unfold produce host_sumcheck.prove_sumcheck_rounds
  simp only [Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_041.complete_result]
  repeat' first
    | with_reducible rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_041.complete_result]
#print axioms complete_result
end PV_L1_Source_042
