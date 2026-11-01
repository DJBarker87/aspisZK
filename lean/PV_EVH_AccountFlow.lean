import PV_EVH_EntropyFlow
import PV_EVH_AccountCallback
set_option autoImplicit false
noncomputable section
namespace PV_EVH_AccountFlow
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World PV_EVH_WorldLoop
open PV_EVH_Prefix (P FinishedView)
open PV_EVH_Entropy (EntropyAnswers)
open PV_EVH_EntropyFlow (Secrets)
variable [ExternalTypes] [ExternalFuns]
abbrev Account (T : Type) := T → Usize → P ((Array U8 32#usize) × T)
abbrev CallbackResult (T : Type) :=
  (core.result.Result Secrets verifier.Error) × T × (T → T)

/-- Source-directed callback. Account acquisition is a named D520 input;
no whole-callback trace is supplied. Both t and back are preserved. -/
def callMut {T : Type}
    (inst : core.ops.function.FnMut T Usize (Array U8 32#usize))
    (fuel : Nat) (answers : EntropyAnswers)
    (entropy : PV_EVH_EntropyStep.Callees) (nonzero_OPEN : Array U8 32#usize → P Bool) (account_OPEN : Account T)
    (c : T) (i : Usize) : P (CallbackResult T) := do
  let (a,t) ← account_OPEN c i
  let r ← PV_EVH_EntropyFlow.generate fuel answers entropy nonzero_OPEN a
  let r1 ← PV_EVH_Prefix.lift (core.result.Result.map_err
    (RealR1_client.prove_for_proof_accounts.closure.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError inst) r ())
  let back := fun c1 : T => c1
  pure (r1,t,back)

/-- The actual FnMut wrapper applies the emitted restoration function. -/
def next {T : Type}
    (inst : core.ops.function.FnMut T Usize (Array U8 32#usize))
    (fuel : Nat) (answers : EntropyAnswers)
    (entropy : PV_EVH_EntropyStep.Callees) (nonzero_OPEN : Array U8 32#usize → P Bool) (account_OPEN : Account T)
    (c : T) (i : Usize) : P ((core.result.Result Secrets verifier.Error) × T) := do
  let (r,c1,back) ← callMut inst fuel answers entropy nonzero_OPEN account_OPEN c i
  pure (r,back c1)

theorem callMut_fixed {T : Type}
    (inst : core.ops.function.FnMut T Usize (Array U8 32#usize))
    (fuel : Nat) (answers : EntropyAnswers)
    (entropy : PV_EVH_EntropyStep.Callees) (nonzero_OPEN : Array U8 32#usize → P Bool) (account_OPEN : Account T)
    (he : PV_EVH_EntropyStep.Compatible entropy)
    (hn : ∀ n, FinishedView (nonzero_OPEN n) (aspis_prover.state_only_entropy.entropy_nonzero32 n))
    (same : ∀ n s, answers n s = getrandom.fill s)
    (account_fixed : ∀ c i, FinishedView (account_OPEN c i) (inst.call_mut c i))
    (c : T) (i : Usize) : FinishedView (callMut inst fuel answers entropy nonzero_OPEN account_OPEN c i)
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut inst c i) := by
  unfold callMut RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
  apply PV_EVH_Prefix.bind_fixed
  · exact account_fixed c i
  · rintro ⟨a,t⟩
    apply PV_EVH_Prefix.bind_fixed
    · exact PV_EVH_EntropyFlow.generate_fixed fuel answers entropy he same nonzero_OPEN hn a
    · intro r
      apply PV_EVH_Prefix.bind_fixed
      · exact PV_EVH_Prefix.lift_fixed _
      · intro r1
        exact PV_EVH_Prefix.lift_fixed _

theorem next_fixed {T : Type}
    (inst : core.ops.function.FnMut T Usize (Array U8 32#usize))
    (fuel : Nat) (answers : EntropyAnswers)
    (entropy : PV_EVH_EntropyStep.Callees) (nonzero_OPEN : Array U8 32#usize → P Bool) (account_OPEN : Account T)
    (he : PV_EVH_EntropyStep.Compatible entropy)
    (hn : ∀ n, FinishedView (nonzero_OPEN n) (aspis_prover.state_only_entropy.entropy_nonzero32 n))
    (same : ∀ n s, answers n s = getrandom.fill s)
    (account_fixed : ∀ c i, FinishedView (account_OPEN c i) (inst.call_mut c i))
    (c : T) (i : Usize) : FinishedView (next inst fuel answers entropy nonzero_OPEN account_OPEN c i)
      ((RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError inst).call_mut c i) := by
  unfold next RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
  apply PV_EVH_Prefix.bind_fixed
  · exact callMut_fixed inst fuel answers entropy nonzero_OPEN account_OPEN he hn same account_fixed c i
  · rintro ⟨r,c1,back⟩
    exact PV_EVH_Prefix.lift_fixed _

#print axioms callMut_fixed
#print axioms next_fixed
end PV_EVH_AccountFlow
