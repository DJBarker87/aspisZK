import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee001
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once` (callee `RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (c : RealR1_client.prove_for_proof_accounts.closure T0) (i : Std.Usize) :
  ∃ next, RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (c := c) (i := i) =
    (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst c i >>= next) := by
  unfold RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee001
