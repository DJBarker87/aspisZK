import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue060
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.semantic_row`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (row : Std.U8) (payload : Slice Std.U8) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) (out : Payload (host_wire.record row payload)) : Result ((core.result.Result aspis_core.field.QM31 r1_wire.Error) ×
    (host_wire.SemanticTranscript H) × (alloc.vec.Vec Std.U8)) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let (r1, transcript1) ←
      host_wire.SemanticTranscript.semantic aspis_coredigestDigest32Inst
        transcript row s
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let s1 := alloc.vec.Vec.deref val
      let bytes1 ←
        alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes s1
      ok (core.result.Result.Ok val1, transcript1, bytes1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual
      ok (r2, transcript1, bytes)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual
    ok (r1, transcript, bytes)

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (row : Std.U8) (payload : Slice Std.U8) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) :
    host_semantic.semantic_row (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (row := row) (payload := payload) (transcript := transcript) (bytes := bytes) =
      (host_wire.record row payload >>= fun out => continueAfter (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (row := row) (payload := payload) (transcript := transcript) (bytes := bytes) out) := by
  rw [host_semantic.semantic_row]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (row : Std.U8) (payload : Slice Std.U8) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) (out : Payload (host_wire.record row payload))
    (h : (host_wire.record row payload) = .ok out) :
    host_semantic.semantic_row (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (row := row) (payload := payload) (transcript := transcript) (bytes := bytes) = continueAfter (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (row := row) (payload := payload) (transcript := transcript) (bytes := bytes) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (row : Std.U8) (payload : Slice Std.U8) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) (e : Error)
    (h : (host_wire.record row payload) = .fail e) :
    host_semantic.semantic_row (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (row := row) (payload := payload) (transcript := transcript) (bytes := bytes) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (row : Std.U8) (payload : Slice Std.U8) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8)
    (h : (host_wire.record row payload) = .div) :
    host_semantic.semantic_row (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (row := row) (payload := payload) (transcript := transcript) (bytes := bytes) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue060
