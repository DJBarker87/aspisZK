import AspisFormal.K1.V7Tag73FiniteSubkernel

/-!
# Repeated restoration: rejection is not a small collision event

This is an explicit adaptive experiment, not a claim that the current root
sweep retries one request. To apply it, prove the exact execution law and the
actual request count. No production scheduling change is proposed here.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73RestorationRetryAccounting
open scoped BigOperators
open AspisK1.V7Tag73FiniteSubkernel
noncomputable section
variable {State Draw : Type*} [Fintype Draw]

/-- Total raw outcome law. Rejection, decode failure and abort must be included
as outcomes: a subprobability deficit would otherwise be mistaken for success. -/
structure AttemptKernel (State Draw : Type*) [Fintype Draw] where
  weight : Draw → ENNReal
  normalized : ∑ d, weight d = 1
  accepts : Draw → Prop
  bad : Draw → Prop
  next : Draw → State

def AttemptKernel.good (k : AttemptKernel State Draw) (d : Draw) : Prop :=
  k.accepts d ∧ ¬ k.bad d

/-- Probability of no good accepted restoration in the next n attempts.
`next` may retain the entire previous history. -/
def retryFailure (policy : State → AttemptKernel State Draw) : Nat → State → ENNReal
  | 0, _ => 1
  | n + 1, s => by
      classical
      exact weighted (policy s).weight
        (fun d => if (policy s).good d then 0
          else retryFailure policy n ((policy s).next d))

theorem retry_nonGood_const (k : AttemptKernel State Draw) (c : ENNReal) :
    weighted k.weight (fun d => if k.good d then 0 else c) =
      eventMass k.weight (fun d => ¬ k.good d) * c := by
  classical
  simp only [weighted, eventMass, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : k.good d <;> simp [hd]

/-- Pointwise continuation bounds suffice; independent identically
 distributed accepted children are not required. -/
theorem retryFailure_le_pow
    (policy : State → AttemptKernel State Draw) (q : ENNReal)
    (noGoodBound : ∀ s, eventMass (policy s).weight
      (fun d => ¬ (policy s).good d) ≤ q)
    (n : Nat) (s : State) : retryFailure policy n s ≤ q ^ n := by
  classical
  induction n generalizing s with
  | zero => simp [retryFailure]
  | succ n ih =>
      simp only [retryFailure]
      calc
        weighted (policy s).weight
            (fun d => if (policy s).good d then 0
              else retryFailure policy n ((policy s).next d)) ≤
          weighted (policy s).weight
            (fun d => if (policy s).good d then 0 else q ^ n) := by
          apply weighted_mono
          intro d
          by_cases hd : (policy s).good d
          · simp [hd]
          · simpa [hd] using ih ((policy s).next d)
        _ = eventMass (policy s).weight (fun d => ¬ (policy s).good d) * q ^ n :=
          retry_nonGood_const (policy s) (q ^ n)
        _ ≤ q * q ^ n := mul_le_mul_right' (noGoodBound s) (q ^ n)
        _ = q ^ (n + 1) := by rw [pow_succ']; rfl

/-- A bad-target bound is not a no-good bound until rejection is counted. -/
theorem retryFailure_le_rejection_add_bad_pow
    (policy : State → AttemptKernel State Draw)
    (rejectionBound badBound : ENNReal)
    (reject : ∀ s, eventMass (policy s).weight
      (fun d => ¬ (policy s).accepts d) ≤ rejectionBound)
    (bad : ∀ s, eventMass (policy s).weight (policy s).bad ≤ badBound)
    (n : Nat) (s : State) :
    retryFailure policy n s ≤ (rejectionBound + badBound) ^ n := by
  apply retryFailure_le_pow policy (rejectionBound + badBound)
  intro t
  exact (not_good_mass_le_reject_add_bad (policy t).weight
      (policy t).accepts (policy t).bad).trans
    (add_le_add (reject t) (bad t))

theorem retryFailure_le_one
    (policy : State → AttemptKernel State Draw) (n : Nat) (s : State) :
    retryFailure policy n s ≤ 1 := by
  classical
  induction n generalizing s with
  | zero => simp [retryFailure]
  | succ n ih =>
      simp only [retryFailure]
      apply weighted_le (policy s).weight (le_of_eq (policy s).normalized) _ 1
      intro d
      by_cases hd : (policy s).good d
      · simp [hd]
      · simpa [hd] using ih ((policy s).next d)

/-- More actual attempts cannot increase the no-good probability. This does
not authorize adding attempts to the production scheduler for free. -/
theorem retryFailure_succ_le
    (policy : State → AttemptKernel State Draw) (n : Nat) (s : State) :
    retryFailure policy (n + 1) s ≤ retryFailure policy n s := by
  classical
  induction n generalizing s with
  | zero => simpa [retryFailure] using retryFailure_le_one policy 1 s
  | succ n ih =>
      simp only [retryFailure]
      apply weighted_mono
      intro d
      by_cases hd : (policy s).good d
      · simp [hd]
      · simpa [hd] using ih ((policy s).next d)

/-- Exact counterexample to dropping rejection mass: every attempt rejects,
no answer is bad, yet extraction by this procedure always fails. -/
def alwaysReject : AttemptKernel Unit Unit where
  weight := fun _ => 1
  normalized := by simp
  accepts := fun _ => False
  bad := fun _ => False
  next := fun _ => ()

theorem alwaysReject_bad_mass_zero :
    eventMass alwaysReject.weight alwaysReject.bad = 0 := by
  simp [eventMass, alwaysReject]

theorem alwaysReject_failure_one (n : Nat) :
    retryFailure (fun _ : Unit => alwaysReject) n () = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [retryFailure, weighted, AttemptKernel.good, alwaysReject] using ih

#print axioms retryFailure_le_pow
#print axioms retryFailure_le_rejection_add_bad_pow
#print axioms retryFailure_succ_le
#print axioms alwaysReject_bad_mass_zero
#print axioms alwaysReject_failure_one
end
end AspisK1.V7Tag73RestorationRetryAccounting
