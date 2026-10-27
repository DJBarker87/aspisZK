import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee024
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut` (callee `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error.call`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (state : host_sumcheck.prove_sumcheck_round.closure H F) (args : Std.Usize) :
  ∃ next, host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut (H := H) (F := F) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (OracleInst := OracleInst) (state := state) (args := args) =
    (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error.call
      aspis_coredigestDigest32Inst OracleInst state args >>= next) := by
  unfold host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee024
