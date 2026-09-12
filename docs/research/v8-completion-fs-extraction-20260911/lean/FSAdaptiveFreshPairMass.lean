import FSFreshQueryMass

/-!
Exact two-step probability law for the actual lazy-oracle interpreter.

The second input may depend on the first answer.  Thus this is the small
adaptive composition lemma needed by the OOD sampler; it is not an
independence assertion inferred from transcript labels.  Both cache misses
are derived from explicit pre-query conditions, and cached executions are
outside this theorem rather than silently resampled.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSAdaptiveFreshPairMass
open scoped BigOperators
open FSOracleExecution FSFreshQueryMass
noncomputable section

universe u v
variable {I : Type u} {O : Type v} [DecidableEq I]

/-- Install the two unread coins without changing any other tape cell. -/
def installPair (tape : Nat → O) (next : Nat) (first second : O) : Nat → O :=
  installNext (installNext tape next first) (next + 1) second

@[simp] theorem installPair_first (tape : Nat → O) (next : Nat) (first second : O) :
    installPair tape next first second next = first := by
  simp [installPair, installNext]

@[simp] theorem installPair_second (tape : Nat → O) (next : Nat) (first second : O) :
    installPair tape next first second (next + 1) = second := by
  simp [installPair, installNext]

/-- The actual sequential interpreter, with the second request selected only
after the first answer is visible. -/
def adaptivePair (tape : Nat → O) (state : State I O) (firstInput : I)
    (secondInput : O → I) : O × O → (O × O) × State I O :=
  fun coins =>
    let installed := installPair tape state.next coins.1 coins.2
    let first := query installed state firstInput
    let second := query installed first.2 (secondInput first.1)
    ((first.1, second.1), second.2)

/-- If every possible adaptive second request was absent from the old cache
and differs from the first request, both returned values are exactly the two
new tape coins.  The hypotheses are prefix facts: they do not freeze the
second input before the first answer. -/
theorem adaptivePair_outputs (tape : Nat → O) (state : State I O)
    (firstInput : I) (secondInput : O → I) (first second : O)
    (firstMiss : state.cache firstInput = none)
    (secondOldMiss : ∀ answer, state.cache (secondInput answer) = none)
    (different : ∀ answer, secondInput answer ≠ firstInput) :
    (adaptivePair tape state firstInput secondInput (first, second)).1 = (first, second) := by
  simp [adaptivePair, query, firstMiss, different first, secondOldMiss first,
    installPair, installNext]

theorem adaptivePair_next (tape : Nat → O) (state : State I O)
    (firstInput : I) (secondInput : O → I) (first second : O)
    (firstMiss : state.cache firstInput = none)
    (secondOldMiss : ∀ answer, state.cache (secondInput answer) = none)
    (different : ∀ answer, secondInput answer ≠ firstInput) :
    (adaptivePair tape state firstInput secondInput (first, second)).2.next =
      state.next + 2 := by
  simp [adaptivePair, query, firstMiss, different first, secondOldMiss first,
    installPair, installNext]

/-- Exact joint mass of two target answers.  In particular, adaptively
choosing the second input after observing the first answer does not bias its
fresh answer. -/
theorem adaptivePair_uniform_targets [Fintype O] [Nonempty O] [DecidableEq O]
    (tape : Nat → O) (state : State I O)
    (firstInput : I) (secondInput : O → I)
    (firstTarget secondTarget : O)
    (firstMiss : state.cache firstInput = none)
    (secondOldMiss : ∀ answer, state.cache (secondInput answer) = none)
    (different : ∀ answer, secondInput answer ≠ firstInput) :
    (∑ first : O, ∑ second : O,
      if (adaptivePair tape state firstInput secondInput (first, second)).1 =
          (firstTarget, secondTarget)
      then (1 : ℚ) else 0) / (Fintype.card O : ℚ) ^ 2 =
        1 / (Fintype.card O : ℚ) ^ 2 := by
  simp only [adaptivePair_outputs tape state firstInput secondInput _ _
    firstMiss secondOldMiss different]
  have numerator :
      (∑ first : O, ∑ second : O,
        if (first, second) = (firstTarget, secondTarget) then (1 : ℚ) else 0) = 1 := by
    classical
    calc
      _ = ∑ first : O, if first = firstTarget then (1 : ℚ) else 0 := by
        apply Finset.sum_congr rfl
        intro first _
        by_cases same : first = firstTarget
        · subst first
          simp
        · simp [same]
      _ = 1 := Fintype.sum_ite_eq' firstTarget (fun _ => (1 : ℚ))
  rw [numerator]

#print axioms adaptivePair_outputs
#print axioms adaptivePair_next
#print axioms adaptivePair_uniform_targets

end
end AspisV8Completion.FSAdaptiveFreshPairMass
