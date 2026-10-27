import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee025
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once` (callee `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (c : host_sumcheck.prove_sumcheck_round.closure H F) (i : Std.Usize) :
  ∃ next, host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once (H := H) (F := F) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (c := c) (i := i) =
    (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
      aspis_coredigestDigest32Inst OracleInst c i >>= next) := by
  unfold host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee025
