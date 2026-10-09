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

/-- Prefix-facing form.  Reachable history validity converts absence from the
chronological log into the two cache misses required above. -/
theorem adaptivePair_uniform_unseen
    [Fintype FSExposureOrder.Block] [Nonempty FSExposureOrder.Block]
    [DecidableEq FSExposureOrder.Block]
    (tape : Nat → FSExposureOrder.Block) (state : FSFirstFresh.Oracle)
    (firstInput : List UInt8)
    (secondInput : FSExposureOrder.Block → List UInt8)
    (firstTarget secondTarget : FSExposureOrder.Block)
    (valid : FSFirstFresh.ValidHistory state)
    (firstUnseen : firstInput ∉ FSExposureOrder.inputs state.log)
    (secondUnseen : ∀ answer, secondInput answer ∉ FSExposureOrder.inputs state.log)
    (different : ∀ answer, secondInput answer ≠ firstInput) :
    (∑ first : FSExposureOrder.Block, ∑ second : FSExposureOrder.Block,
      if (adaptivePair tape state firstInput secondInput (first, second)).1 =
          (firstTarget, secondTarget)
      then (1 : ℚ) else 0) / (Fintype.card FSExposureOrder.Block : ℚ) ^ 2 =
        1 / (Fintype.card FSExposureOrder.Block : ℚ) ^ 2 :=
  adaptivePair_uniform_targets tape state firstInput secondInput
    firstTarget secondTarget
    (cache_miss_of_unseen state valid firstInput firstUnseen)
    (fun answer => cache_miss_of_unseen state valid (secondInput answer)
      (secondUnseen answer))
    different

abbrev outputInput (digest : FSExposureOrder.Block) : List UInt8 :=
  FSExposureOrder.squeezeInput digest

def advanceInput (digest : FSExposureOrder.Block) : List UInt8 :=
  FSExposureOrder.blockBytes digest ++ [2]

theorem advanceInput_ne_outputInput (digest : FSExposureOrder.Block) :
    advanceInput digest ≠ outputInput digest := by
  intro same
  have last := congrArg List.getLast? same
  simp [advanceInput, outputInput, FSExposureOrder.squeezeInput] at last

/-- Exact joint law for the two literal source queries made by one squeeze.
The two byte strings must both be unseen at the starting prefix; if either was
queried earlier, that execution belongs to the separately charged target-hit
case rather than this law. -/
theorem sourceSqueeze_uniform_targets
    (tape : Nat → FSExposureOrder.Block) (state : FSFirstFresh.Oracle)
    (digest firstTarget secondTarget : FSExposureOrder.Block)
    (valid : FSFirstFresh.ValidHistory state)
    (outputUnseen : outputInput digest ∉ FSExposureOrder.inputs state.log)
    (advanceUnseen : advanceInput digest ∉ FSExposureOrder.inputs state.log) :
    (∑ first : FSExposureOrder.Block, ∑ second : FSExposureOrder.Block,
      if (adaptivePair tape state (outputInput digest) (fun _ => advanceInput digest)
          (first, second)).1 = (firstTarget, secondTarget)
      then (1 : ℚ) else 0) / (Fintype.card FSExposureOrder.Block : ℚ) ^ 2 =
        1 / (Fintype.card FSExposureOrder.Block : ℚ) ^ 2 :=
  adaptivePair_uniform_unseen tape state (outputInput digest)
    (fun _ => advanceInput digest) firstTarget secondTarget valid outputUnseen
    (fun _ => advanceUnseen) (fun _ => advanceInput_ne_outputInput digest)

#print axioms adaptivePair_outputs
#print axioms adaptivePair_next
#print axioms adaptivePair_uniform_targets
#print axioms adaptivePair_uniform_unseen
#print axioms sourceSqueeze_uniform_targets

end
end AspisV8Completion.FSAdaptiveFreshPairMass
