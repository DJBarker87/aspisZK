import AspisV8R17.AdaptiveOracle
import AspisV8R17.FirstAssignment

/-! Refinement between the complete-oracle causal interpreter and the retained
R9 queryStep cache. No independent fresh answer is supplied on a cache hit. -/
set_option autoImplicit false
namespace AspisV8R17.AdaptiveMemoized
open AspisV8PairedCommitment AspisV8R17.AdaptiveOracle
variable {I A : Type} [DecidableEq I]

def Compatible (H : I → A) (t : Table I A) : Prop :=
  ∀ i a, t i = some a → a = H i

theorem query_answer (H : I → A) (t : Table I A) (hc : Compatible H t) (i : I) :
    (queryStep t i (H i)).1 = H i := by
  cases found : t i with
  | none => simp [queryStep, found]
  | some a => simpa [queryStep, found] using hc i a found

theorem query_compatible (H : I → A) (t : Table I A) (hc : Compatible H t) (i : I) :
    Compatible H (queryStep t i (H i)).2 := by
  intro j a ha
  obtain old | ⟨_, rfl, rfl⟩ := query_lookup_origin t i (H i) j a ha
  · exact hc j a old
  · rfl

def memoRun (next : List (I × A) → I) (H : I → A) :
    ℕ → List (I × A) → Table I A → List (I × A)
  | 0, _, _ => []
  | n+1, history, t =>
    let i := next history
    let step := queryStep t i (H i)
    (i,step.1) :: memoRun next H n (history ++ [(i,step.1)]) step.2

theorem memoRun_eq_run (next : List (I × A) → I) (H : I → A)
    (n : ℕ) (history : List (I × A)) (t : Table I A) (hc : Compatible H t) :
    memoRun next H n history t = run next H n history := by
  induction n generalizing history t with
  | zero => rfl
  | succ n ih =>
    simp only [memoRun, run, query_answer H t hc]
    congr 1
    exact ih _ _ (query_compatible H t hc _)

theorem query_missing_iff (t : Table I A) (input i : I) (fresh : A) :
    (queryStep t input fresh).2 i = none ↔ t i = none ∧ i ≠ input := by
  by_cases hi : i=input
  · subst i
    cases found : t input <;> simp [queryStep, found, put]
  · cases found : t input <;> simp [queryStep, found, put, hi]

theorem cache_missing_iff (calls : List (I × A)) (t : Table I A) (i : I) :
    runQueries t calls i = none ↔ t i = none ∧ ∀ p ∈ calls, p.1 ≠ i := by
  induction calls generalizing t with
  | nil => simp [runQueries]
  | cons p calls ih =>
    simp only [runQueries, ih, query_missing_iff, List.mem_cons,
      forall_eq_or_imp]
    simp [and_assoc, and_left_comm, and_comm, ne_comm]

theorem empty_memoRun (next : List (I × A) → I) (H : I → A) (n : ℕ) :
    memoRun next H n [] (fun _ => none) = run next H n [] :=
  memoRun_eq_run next H n [] _ (by intro i a h; cases h)

theorem memoized_fresh_joint_probabilities [Fintype I] [Fintype A] [Nonempty A]
    [DecidableEq A] (next : List (I × A) → I) (n : ℕ) (tr : List (I × A))
    (missing : runQueries (fun _ => none) tr (next tr) = none) (a b : A) :
    AspisV8Privacy.uniformProbability
      (fun H : I → A => (memoRun next H n [] (fun _ => none), H (next tr))) (tr,a) =
    AspisV8Privacy.uniformProbability
      (fun H : I → A => (memoRun next H n [] (fun _ => none), H (next tr))) (tr,b) := by
  simp only [empty_memoRun]
  exact fresh_next_joint_probabilities next n tr
    ((cache_missing_iff tr (fun _ => none) (next tr)).mp missing).2 a b

#print axioms query_answer
#print axioms query_compatible
#print axioms memoRun_eq_run
#print axioms query_missing_iff
#print axioms cache_missing_iff
#print axioms empty_memoRun
#print axioms memoized_fresh_joint_probabilities
end AspisV8R17.AdaptiveMemoized
