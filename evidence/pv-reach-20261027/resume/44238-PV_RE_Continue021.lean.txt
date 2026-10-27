import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue021
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.zc_rows`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) (out : Payload (aspis_core.field.QM31.ZERO)) : Result ((core.result.Result (Array aspis_core.field.QM31 10#usize)
    r1_wire.Error) × (host_wire.SemanticTranscript H) × (alloc.vec.Vec
    Std.U8)) := do
  let q := out
  let zc := Array.repeat 10#usize q
  let (transcript1, bytes1, zc1, pending_return) ←
    host_semantic.zc_rows_loop aspis_coredigestDigest32Inst transcript bytes zc
      0#usize
  match pending_return with
  | none => ok (core.result.Result.Ok zc1, transcript1, bytes1)
  | some r => ok (r, transcript1, bytes1)

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) :
    host_semantic.zc_rows (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (transcript := transcript) (bytes := bytes) =
      (aspis_core.field.QM31.ZERO >>= fun out => continueAfter (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (transcript := transcript) (bytes := bytes) out) := by
  rw [host_semantic.zc_rows]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) (out : Payload (aspis_core.field.QM31.ZERO))
    (h : (aspis_core.field.QM31.ZERO) = .ok out) :
    host_semantic.zc_rows (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (transcript := transcript) (bytes := bytes) = continueAfter (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (transcript := transcript) (bytes := bytes) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) (e : Error)
    (h : (aspis_core.field.QM31.ZERO) = .fail e) :
    host_semantic.zc_rows (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (transcript := transcript) (bytes := bytes) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8)
    (h : (aspis_core.field.QM31.ZERO) = .div) :
    host_semantic.zc_rows (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (transcript := transcript) (bytes := bytes) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue021
