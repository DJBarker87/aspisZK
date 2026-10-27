import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue063
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (c : host_sumcheck.prove_sumcheck_round.closure H F) (i : Std.Usize) (out : Payload (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
      aspis_coredigestDigest32Inst OracleInst c i)) : Result (core.result.Result aspis_core.field.QM31 r1_wire.Error) := do
  let (r, _) := out
  ok r

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (c : host_sumcheck.prove_sumcheck_round.closure H F) (i : Std.Usize) :
    host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once (H := H) (F := F) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (c := c) (i := i) =
      (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
      aspis_coredigestDigest32Inst OracleInst c i >>= fun out => continueAfter (H := H) (F := F) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (c := c) (i := i) out) := by
  rw [host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (c : host_sumcheck.prove_sumcheck_round.closure H F) (i : Std.Usize) (out : Payload (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
      aspis_coredigestDigest32Inst OracleInst c i))
    (h : (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
      aspis_coredigestDigest32Inst OracleInst c i) = .ok out) :
    host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once (H := H) (F := F) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (c := c) (i := i) = continueAfter (H := H) (F := F) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (c := c) (i := i) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (c : host_sumcheck.prove_sumcheck_round.closure H F) (i : Std.Usize) (e : Error)
    (h : (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
      aspis_coredigestDigest32Inst OracleInst c i) = .fail e) :
    host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once (H := H) (F := F) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (c := c) (i := i) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (c : host_sumcheck.prove_sumcheck_round.closure H F) (i : Std.Usize)
    (h : (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
      aspis_coredigestDigest32Inst OracleInst c i) = .div) :
    host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once (H := H) (F := F) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (c := c) (i := i) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue063
