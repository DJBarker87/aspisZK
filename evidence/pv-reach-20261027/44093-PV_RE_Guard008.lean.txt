import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Guard008
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def onTrue {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (self : host_wire.SemanticTranscript H) (row : Std.U8) (framed : Slice Std.U8) : Result ((core.result.Result (Array Std.U8 32#usize) r1_wire.Error) ×
    (host_wire.SemanticTranscript H)) := do
    ok (core.result.Result.Err (r1_wire.Error.RowOrder self.next_row row),
      self)

def onFalse {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (self : host_wire.SemanticTranscript H) (row : Std.U8) (framed : Slice Std.U8) : Result ((core.result.Result (Array Std.U8 32#usize) r1_wire.Error) ×
    (host_wire.SemanticTranscript H)) := do
    let s ← Aeneas.Std.lift (Array.to_slice self.state)
    let i ← Aeneas.Std.lift (Std.U8.wrapping_add 160#u8 row)
    let s1 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ 0#u8, i ]))
    let s2 ← Aeneas.Std.lift (Array.to_slice (Array.make 3#usize [ s, s1, framed ]))
    let absorbed ← aspis_coredigestDigest32Inst.digest self.hash s2
    let s3 ← Aeneas.Std.lift (Array.to_slice absorbed)
    let s4 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
    let s5 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s3, s4 ]))
    let block ← aspis_coredigestDigest32Inst.digest self.hash s5
    let s6 ← Aeneas.Std.lift (Array.to_slice absorbed)
    let s7 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
    let s8 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s6, s7 ]))
    let a ← aspis_coredigestDigest32Inst.digest self.hash s8
    let i1 ← Aeneas.Std.lift (Std.U8.wrapping_add self.next_row 1#u8)
    ok (core.result.Result.Ok block, { self with state := a, next_row := i1 })

/-- Exact first guard of `host_wire.SemanticTranscript.sample_block_validated`.
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (self : host_wire.SemanticTranscript H) (row : Std.U8) (framed : Slice Std.U8) :
  host_wire.SemanticTranscript.sample_block_validated (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (self := self) (row := row) (framed := framed) =
    (if row != self.next_row then onTrue (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (self := self) (row := row) (framed := framed) else onFalse (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (self := self) (row := row) (framed := framed)) := by
  rw [host_wire.SemanticTranscript.sample_block_validated]
  rfl

#print axioms onTrue
#print axioms onFalse
#print axioms first
end R1Z.PV_RE_Guard008
