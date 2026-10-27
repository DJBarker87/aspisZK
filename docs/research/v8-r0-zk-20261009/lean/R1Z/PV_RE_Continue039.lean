import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue039
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once`.
Recursive calls remain the original extracted calls. -/
def continueAfter {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (c : RealR1_client.prove_for_proof_accounts.closure T0) (i : Std.Usize) (out : Payload (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst c i)) : Result ((core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets verifier.Error) ×
    (RealR1_client.prove_for_proof_accounts.closure T0)) := do
  let (r, c1, call_mut_back) := out
  ok (r, call_mut_back c1)

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (c : RealR1_client.prove_for_proof_accounts.closure T0) (i : Std.Usize) :
    RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (c := c) (i := i) =
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst c i >>= fun out => continueAfter (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (c := c) (i := i) out) := by
  rw [RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (c : RealR1_client.prove_for_proof_accounts.closure T0) (i : Std.Usize) (out : Payload (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst c i))
    (h : (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst c i) = .ok out) :
    RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (c := c) (i := i) = continueAfter (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (c := c) (i := i) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (c : RealR1_client.prove_for_proof_accounts.closure T0) (i : Std.Usize) (e : Error)
    (h : (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst c i) = .fail e) :
    RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (c := c) (i := i) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (c : RealR1_client.prove_for_proof_accounts.closure T0) (i : Std.Usize)
    (h : (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst c i) = .div) :
    RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (c := c) (i := i) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue039
