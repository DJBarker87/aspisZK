import AspisV8R19.R607FieldSetMass
import AspisV8R19.R609CircleRetryLaw
import AspisV8R19.R592FiniteBlockExecution
import AspisV8R19.R600ResultEvalLength

/-! Mean-level ordinary independent sampler observation law.

The reduction below is through `R592FiniteBlockExecution`'s finite block mean.
It never states an independent-Program support premise inferred from a
particular deterministic oracle run.
-/
set_option autoImplicit false
namespace AspisV8R19.R935OrdinaryObservationLaw

open MemoizedProgramLaw OracleResampling
open R580SourceWordStream R572SequentialWordMass R589IndexedReplyExecution
open R584IndependentBlockSampler R594JointChallengeMass R599CanonicalFieldTuple
open R607FieldSetMass R609CircleRetryLaw R592FiniteBlockExecution
open R600ResultEvalLength R445InitialBlockRejectionLaw
open SourceDuplexStep QM31SamplerProgram
open scoped BigOperators
noncomputable section

abbrev Tuple := Fin 4 → Fin modulus

def encodeTuple (x : Tuple) : List Nat := (List.ofFn x).map Fin.val

def missingEvent (out : Option (List Nat)) : ℚ := if out = none then 1 else 0

def expanded (test : Option (List Nat) → ℚ) (out : Option (List Nat)) : ℚ :=
  missingEvent out * test none +
    ∑ x : Tuple, tupleEvent x out * test (some (encodeTuple x))

private theorem encodeTuple_eq_iff (x y : Tuple) :
    encodeTuple x = encodeTuple y ↔ x = y := by
  constructor
  · intro h
    apply tupleFieldEquiv.injective
    change tupleField x = tupleField y
    change (List.ofFn x).map Fin.val = (List.ofFn y).map Fin.val at h
    rw [← listDecode_tuple x, ← listDecode_tuple y, h]
  · intro h
    subst y
    rfl

private theorem canonical_partition (test : Option (List Nat) → ℚ)
    (xs : List Nat) (hlen : xs.length = 4)
    (hcan : ∀ a ∈ xs, a < modulus) :
    test (some xs) =
      ∑ x : Tuple, tupleEvent x (some xs) * test (some (encodeTuple x)) := by
  let x0 : Tuple := tupleFieldEquiv.symm (SamplerFieldDecode.decode xs)
  have hdecode : SamplerFieldDecode.decode xs = tupleField x0 := by
    exact (tupleFieldEquiv.apply_symm_apply _).symm
  have hx0 : xs = encodeTuple x0 := by
    exact (decode_eq_tuple_iff hlen hcan x0).mp hdecode
  rw [hx0]
  simp only [tupleEvent, Option.some.injEq]
  change test (some (encodeTuple x0)) =
    ∑ x : Tuple, (if encodeTuple x0 = encodeTuple x then (1 : ℚ) else 0) *
      test (some (encodeTuple x))
  simp [encodeTuple_eq_iff]

/-- Congruence at the exact finite-block mean, requiring agreement only at the
outcomes constructed by `resultEval` (none or a four-list of `Fin modulus`). -/
private theorem challenge_observer_congr
    (f g : Option (List Nat) → ℚ)
    (hnone : f none = g none)
    (hcanon : ∀ x : Tuple, f (some (encodeTuple x)) = g (some (encodeTuple x)))
    (s : State) :
    outputMean (challengeProgram s) (fun r => f r.1) =
      outputMean (challengeProgram s) (fun r => g r.1) := by
  simp only [challenge_independent_block, independent_block_result_law]
  apply mean_congr
  intro blocks
  generalize hr : resultEval (blockAnswer (extendBlocks blocks)) (limbs 8 4 0) = r
  rcases r with ⟨out, next⟩
  cases out with
  | none => simpa only [Option.map_none] using hnone
  | some xs =>
      have hlen : xs.length = 4 :=
        resultEval_limbs_length (blockAnswer (extendBlocks blocks)) 8 4 0 hr
      obtain ⟨a, b, c, d, hxs⟩ : ∃ a b c d, xs = [a, b, c, d] :=
        ⟨_, _, _, _, List.eq_getElem_of_length_eq_four xs hlen⟩
      subst xs
      let x : Tuple := ![a, b, c, d]
      have hx : encodeTuple x = [a.val, b.val, c.val, d.val] := by
        simp [encodeTuple, x, ofFn_four_values]
      simpa only [Option.map_some, List.map_cons, List.map_nil, ← hx] using hcanon x

private theorem expanded_none (test : Option (List Nat) → ℚ) :
    expanded test none = test none := by
  simp only [expanded, missingEvent, if_pos rfl, tupleEvent]
  simp

private theorem expanded_canonical (test : Option (List Nat) → ℚ)
    (x : Tuple) : expanded test (some (encodeTuple x)) =
      test (some (encodeTuple x)) := by
  rw [expanded]
  simp only [missingEvent, Option.some_ne_none, if_false, zero_mul, zero_add]
  symm
  apply canonical_partition test (encodeTuple x)
  · simp [encodeTuple]
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact b.isLt

/-- Every raw-list observer of the ordinary independent challenge is its
explicit failure value plus the exact equal mass of all canonical four-tuples. -/
theorem ordinary_observation_law
    (test : Option (List Nat) → ℚ) (s : State) :
    outputMean (challengeProgram s) (fun r => test r.1) =
      (1 - (modulus ^ 4 : Nat) * lambda) * test none +
        lambda * ∑ x : Tuple, test (some (encodeTuple x)) := by
  calc
    outputMean (challengeProgram s) (fun r => test r.1) =
      outputMean (challengeProgram s) (fun r => expanded test r.1) := by
        symm
        apply challenge_observer_congr (expanded test) test
        · exact expanded_none test
        · intro x
          exact expanded_canonical test x
    _ = outputMean (challengeProgram s) (fun r => missingEvent r.1 * test none) +
          outputMean (challengeProgram s)
            (fun r => ∑ x : Tuple, tupleEvent x r.1 * test (some (encodeTuple x))) := by
          exact outputMean_add _ _ _
    _ = outputMean (challengeProgram s) (fun r => missingEvent r.1) * test none +
          ∑ x : Tuple,
            outputMean (challengeProgram s) (fun r => tupleEvent x r.1) *
              test (some (encodeTuple x)) := by
          simp only [outputMean_mul, outputMean_finset_sum]
    _ = (1 - (modulus ^ 4 : Nat) * lambda) * test none +
          ∑ x : Tuple, lambda * test (some (encodeTuple x)) := by
          rw [show missingEvent = R609CircleRetryLaw.missing by rfl,
            independent_missing_mass]
          have hm (x : Tuple) : outputMean (challengeProgram s)
              (fun r => tupleEvent x r.1) = lambda :=
            source_independent_tuple_mass s x
          simp only [hm]
    _ = (1 - (modulus ^ 4 : Nat) * lambda) * test none +
          lambda * ∑ x : Tuple, test (some (encodeTuple x)) := by
          rw [Finset.mul_sum]

/-- The direct error-zero specialization does not condition the challenge
program; it evaluates the existing explicit failure term. -/
theorem ordinary_observation_law_error_zero
    (test : Option (List Nat) → ℚ) (s : State) (hnone : test none = 0) :
    outputMean (challengeProgram s) (fun r => test r.1) =
      lambda * ∑ x : Tuple, test (some (encodeTuple x)) := by
  rw [ordinary_observation_law test s, hnone]
  ring

#print axioms encodeTuple_eq_iff
#print axioms canonical_partition
#print axioms challenge_observer_congr
#print axioms expanded_none
#print axioms expanded_canonical
#print axioms encodeTuple
#print axioms missingEvent
#print axioms expanded
#print axioms ordinary_observation_law
#print axioms ordinary_observation_law_error_zero

end
end AspisV8R19.R935OrdinaryObservationLaw
