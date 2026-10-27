import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee011
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut` (callee `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (state : host_commitment.encode_commitment_words.closure_1) (args : Std.Usize) :
  ∃ next, host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut (state := state) (args := args) =
    (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call
      state args >>= next) := by
  unfold host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee011
