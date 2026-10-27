import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee012
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once` (callee `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (c : host_commitment.encode_commitment_words.closure_1) (i : Std.Usize) :
  ∃ next, host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once (c := c) (i := i) =
    (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
      c i >>= next) := by
  unfold host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee012
