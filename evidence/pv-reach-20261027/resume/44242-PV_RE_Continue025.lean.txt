import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue025
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.prove_sumcheck`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle T1) (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8) (initial_claim : aspis_core.field.QM31) (oracle : T1) (out : Payload (aspis_core.field.QM31.ZERO)) : Result ((core.result.Result ((Array aspis_core.field.QM31 10#usize) ×
    aspis_core.field.QM31) r1_wire.Error) × (host_wire.SemanticTranscript H)
    × (alloc.vec.Vec Std.U8)) := do
  let q := out
  let a := Array.repeat 10#usize q
  host_sumcheck.prove_sumcheck_rounds aspis_coredigestDigest32Inst OracleInst
    transcript output a initial_claim 0#usize oracle

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle T1) (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8) (initial_claim : aspis_core.field.QM31) (oracle : T1) :
    host_sumcheck.prove_sumcheck (H := H) (T1 := T1) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (transcript := transcript) (output := output) (initial_claim := initial_claim) (oracle := oracle) =
      (aspis_core.field.QM31.ZERO >>= fun out => continueAfter (H := H) (T1 := T1) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (transcript := transcript) (output := output) (initial_claim := initial_claim) (oracle := oracle) out) := by
  rw [host_sumcheck.prove_sumcheck]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle T1) (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8) (initial_claim : aspis_core.field.QM31) (oracle : T1) (out : Payload (aspis_core.field.QM31.ZERO))
    (h : (aspis_core.field.QM31.ZERO) = .ok out) :
    host_sumcheck.prove_sumcheck (H := H) (T1 := T1) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (transcript := transcript) (output := output) (initial_claim := initial_claim) (oracle := oracle) = continueAfter (H := H) (T1 := T1) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (transcript := transcript) (output := output) (initial_claim := initial_claim) (oracle := oracle) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle T1) (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8) (initial_claim : aspis_core.field.QM31) (oracle : T1) (e : Error)
    (h : (aspis_core.field.QM31.ZERO) = .fail e) :
    host_sumcheck.prove_sumcheck (H := H) (T1 := T1) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (transcript := transcript) (output := output) (initial_claim := initial_claim) (oracle := oracle) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle T1) (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8) (initial_claim : aspis_core.field.QM31) (oracle : T1)
    (h : (aspis_core.field.QM31.ZERO) = .div) :
    host_sumcheck.prove_sumcheck (H := H) (T1 := T1) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (transcript := transcript) (output := output) (initial_claim := initial_claim) (oracle := oracle) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue025
