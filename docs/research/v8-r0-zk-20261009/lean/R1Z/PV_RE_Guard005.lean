import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Guard005
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def onTrue {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8) (point : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Std.Usize) (oracle : F) : Result ((core.result.Result ((Array aspis_core.field.QM31 10#usize) ×
    aspis_core.field.QM31) r1_wire.Error) × (host_wire.SemanticTranscript H)
    × (alloc.vec.Vec Std.U8)) := do
    let r ← OracleInst.evaluate oracle point
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let b ←
        core.cmp.PartialEq.ne.trait_default
          aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 val running
      if b
      then
        ok (core.result.Result.Err r1_wire.Error.Terminal, transcript, output)
      else ok (core.result.Result.Ok (point, running), transcript, output)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
          (core.convert.FromSame r1_wire.Error) residual
      ok (r1, transcript, output)

def onFalse {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8) (point : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Std.Usize) (oracle : F) : Result ((core.result.Result ((Array aspis_core.field.QM31 10#usize) ×
    aspis_core.field.QM31) r1_wire.Error) × (host_wire.SemanticTranscript H)
    × (alloc.vec.Vec Std.U8)) := do
    let (r, transcript1, output1) ←
      host_sumcheck.prove_sumcheck_round aspis_coredigestDigest32Inst
        OracleInst transcript output point running round oracle
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (point1, running1) := val
      let i ← Aeneas.Std.lift (Std.Usize.wrapping_add round 1#usize)
      host_sumcheck.prove_sumcheck_rounds aspis_coredigestDigest32Inst
        OracleInst transcript1 output1 point1 running1 i oracle
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
          (core.convert.FromSame r1_wire.Error) residual
      ok (r1, transcript1, output1)

/-- Exact first guard of `host_sumcheck.prove_sumcheck_rounds`.
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8) (point : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Std.Usize) (oracle : F) :
  host_sumcheck.prove_sumcheck_rounds (H := H) (F := F) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (transcript := transcript) (output := output) (point := point) (running := running) (round := round) (oracle := oracle) =
    (if round = 10#usize then onTrue (H := H) (F := F) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (transcript := transcript) (output := output) (point := point) (running := running) (round := round) (oracle := oracle) else onFalse (H := H) (F := F) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (transcript := transcript) (output := output) (point := point) (running := running) (round := round) (oracle := oracle)) := by
  rw [host_sumcheck.prove_sumcheck_rounds]
  rfl

#print axioms onTrue
#print axioms onFalse
#print axioms first
end R1Z.PV_RE_Guard005
