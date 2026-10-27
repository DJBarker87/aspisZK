import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Guard007
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def onTrue {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (self : host_wire.SemanticTranscript H) (row : Std.U8) (framed : Slice Std.U8) : Result ((core.result.Result (Array Std.U8 32#usize) r1_wire.Error) ×
    (host_wire.SemanticTranscript H)) := do
    ok (core.result.Result.Err (r1_wire.Error.RowOrder self.next_row row),
      self)

def onFalse {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (self : host_wire.SemanticTranscript H) (row : Std.U8) (framed : Slice Std.U8) : Result ((core.result.Result (Array Std.U8 32#usize) r1_wire.Error) ×
    (host_wire.SemanticTranscript H)) := do
    let r ← host_wire.parse_record row framed
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      host_wire.SemanticTranscript.sample_block_validated
        aspis_coredigestDigest32Inst self row framed
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array Std.U8 32#usize) (core.convert.FromSame r1_wire.Error)
          residual
      ok (r1, self)

/-- Exact first guard of `host_wire.SemanticTranscript.sample_block`.
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (self : host_wire.SemanticTranscript H) (row : Std.U8) (framed : Slice Std.U8) :
  host_wire.SemanticTranscript.sample_block (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (self := self) (row := row) (framed := framed) =
    (if row != self.next_row then onTrue (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (self := self) (row := row) (framed := framed) else onFalse (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (self := self) (row := row) (framed := framed)) := by
  rw [host_wire.SemanticTranscript.sample_block]
  rfl

#print axioms onTrue
#print axioms onFalse
#print axioms first
end R1Z.PV_RE_Guard007
