import R1Z.PV_RE_FiniteRetry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientFinite
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes] [ExternalFuns]

theorem bind_assoc {A B C : Type} (x : Result A)
    (f : A → Result B) (g : B → Result C) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
  cases x <;> rfl

/-- Complete outer proof-account control equation. The variant callback is
kept as an actual call, including its failures, divergence and both booleans.
The successful branch contains all eight possible retry positions. -/
theorem equation {C : Type}
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (pub : Public) (compiled : Compiled) (hash : Hash) (store : Store) (state : C) :
    RealR1_client.prove_for_proof_accounts entropy pub compiled hash store state =
      (ExternalFuns.op233 .S2 .S2 >>= fun equal =>
        if !equal then .ok (.Err .Semantic, store)
        else PV_RE_FiniteRetry.runN
          (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError entropy)
          pub compiled .S2 hash 8 store state 0#usize) := by
  unfold RealR1_client.prove_for_proof_accounts prover.prove_masked_retrying_with
    core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
    transport.Variant.Insts.CoreCmpPartialEqVariant
  simp only [bind_assoc]
  congr 1
  funext equal
  cases equal with
  | false => rfl
  | true =>
    change (prover.retry_attempt _ pub compiled .S2 hash store state 0#usize >>=
      fun p => .ok (p.1,p.2)) = _
    rw [PV_RE_FiniteRetry.at0]
    cases PV_RE_FiniteRetry.runN
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError entropy)
      pub compiled .S2 hash 8 store state 0#usize <;> rfl

#print axioms bind_assoc
#print axioms equation
end R1Z.PV_RE_ClientFinite
