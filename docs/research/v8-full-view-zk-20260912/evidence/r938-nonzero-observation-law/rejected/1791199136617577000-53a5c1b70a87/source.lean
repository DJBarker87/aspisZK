import AspisV8R19.R935OrdinaryObservationLaw
import AspisV8R19.R932NonzeroIndependentMass

/-! Full-observer law for the bounded nonzero wrapper in the independent model.

The observer is arbitrary rational
valued: no positivity, normalization, or success conditioning is used.
-/
set_option autoImplicit false
namespace AspisV8R19.R938NonzeroObservationLaw

open MemoizedProgramLaw OracleProgramOps OracleResampling
open R584IndependentBlockSampler R594JointChallengeMass R599CanonicalFieldTuple
open R609CircleRetryLaw R932NonzeroIndependentMass
open R935OrdinaryObservationLaw
open SourceDuplexStep BoundedSamplerWrapper SamplerWrapperPolicies
open R445InitialBlockRejectionLaw (modulus)
open scoped BigOperators
noncomputable section

abbrev Tuple := R935OrdinaryObservationLaw.Tuple
abbrev Error := SamplerWrapperPolicies.Error

def zeroTuple : Tuple := fun _ => 0

def zeroRaw : List Nat := [0, 0, 0, 0]

def successfulSum (test : Except Error (List Nat) → ℚ) : ℚ :=
  ∑ x : Tuple,
    if encodeTuple x = zeroRaw then 0 else test (.ok (encodeTuple x))

def expected (n : Nat) (test : Except Error (List Nat) → ℚ) : ℚ :=
  (lambda ^ n + (1 - (modulus ^ 4 : Nat) * lambda) * retrySum n) *
      test (.error .challengeExhausted) +
    lambda * retrySum n * successfulSum test

private theorem encode_zeroTuple : encodeTuple zeroTuple = zeroRaw := by
  simp [encodeTuple, zeroTuple, zeroRaw, ofFn_four_values]

private theorem encodeTuple_zero_iff (x : Tuple) :
    encodeTuple x = zeroRaw ↔ x = zeroTuple := by
  constructor
  · intro h
    apply tupleFieldEquiv.injective
    change tupleField x = tupleField zeroTuple
    rw [← listDecode_tuple x, ← listDecode_tuple zeroTuple]
    change encodeTuple x = encodeTuple zeroTuple
    rw [encode_zeroTuple]
    exact h
  · intro h
    subst x
    exact encode_zeroTuple

/-- The canonical tuple sum seen by one wrapper stage: exactly the all-zero
atom continues, and every other tuple is passed to the observer. -/
private theorem stage_sum
    (test : Except Error (List Nat) → ℚ) (tail : ℚ) :
    ∑ x : Tuple,
      (if encodeTuple x = zeroRaw then tail else test (.ok (encodeTuple x))) =
      tail + successfulSum test := by
  classical
  have hpoint (x : Tuple) :
      (if encodeTuple x = zeroRaw then tail else test (.ok (encodeTuple x))) =
        (if x = zeroTuple then tail else 0) +
          (if encodeTuple x = zeroRaw then 0 else test (.ok (encodeTuple x))) := by
    by_cases h : x = zeroTuple
    · subst x
      simp [encode_zeroTuple]
    · have hn : encodeTuple x ≠ zeroRaw := by
        intro hh
        exact h ((encodeTuple_zero_iff x).mp hh)
      simp [h, hn]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- Arbitrary signed-observer law for every retry cap and starting state. -/
theorem nonzero_observation_law
    (test : Except Error (List Nat) → ℚ) :
    ∀ (n : Nat) (s : State),
      outputMean
        (BoundedSamplerWrapper.program nonzeroAccept
          Error.challengeExhausted Error.challengeExhausted n s)
        (fun r => test r.1) = expected n test := by
  intro n
  induction n with
  | zero =>
      intro s
      simp [BoundedSamplerWrapper.program, outputMean_done, expected, retrySum,
        successfulSum]
  | succ n ih =>
      intro s
      rw [BoundedSamplerWrapper.program, outputMean_bind]
      let tail := expected n test
      let stage : Option (List Nat) → ℚ := fun out =>
        match out with
        | none => test (.error .challengeExhausted)
        | some xs => if xs = zeroRaw then tail else test (.ok xs)
      have hcontinuation : ∀ r : Option (List Nat) × State,
          outputMean
            (match r.1 with
            | none => .done (.error Error.challengeExhausted, r.2)
            | some xs => match nonzeroAccept xs with
              | some y => .done (.ok y, r.2)
              | none => BoundedSamplerWrapper.program nonzeroAccept
                  Error.challengeExhausted Error.challengeExhausted n r.2)
            (fun v => test v.1) = stage r.1 := by
        intro r
        rcases r with ⟨out, t⟩
        cases out with
        | none =>
            simp [stage, outputMean_done]
        | some xs =>
            dsimp only
            by_cases hz : xs = zeroRaw
            · subst xs
              have hreject : nonzeroAccept zeroRaw = none := by rfl
              rw [hreject]
              simpa only [stage, if_pos rfl] using ih t
            · have haccept : nonzeroAccept xs = some xs := if_neg hz
              rw [haccept]
              simp [stage, hz, outputMean_done]
      calc
        outputMean (QM31SamplerProgram.challengeProgram s)
          (fun r => outputMean
            (match r.1 with
            | none => .done (.error Error.challengeExhausted, r.2)
            | some xs => match nonzeroAccept xs with
              | some y => .done (.ok y, r.2)
              | none => BoundedSamplerWrapper.program nonzeroAccept
                  Error.challengeExhausted Error.challengeExhausted n r.2)
            (fun v => test v.1)) =
          outputMean (QM31SamplerProgram.challengeProgram s) (fun r => stage r.1) := by
            apply outputMean_congr
            intro r
            exact hcontinuation r
        _ = (1 - (modulus ^ 4 : Nat) * lambda) * test (.error .challengeExhausted) +
            lambda * ∑ x : Tuple,
              if encodeTuple x = zeroRaw then tail else test (.ok (encodeTuple x)) := by
            rw [ordinary_observation_law stage s]
            simp only [stage]
        _ = (1 - (modulus ^ 4 : Nat) * lambda) * test (.error .challengeExhausted) +
            lambda * (tail + successfulSum test) := by rw [stage_sum test tail]
        _ = expected (n + 1) test := by
            dsimp [tail, expected]
            rw [retrySum, pow_succ]
            ring

/-- The literal selected cap-three policy is a direct specialization, retaining
its exhaustion event rather than conditioning it away. -/
theorem nonzeroProgram_observation_law
    (test : Except Error (List Nat) → ℚ) (s : State) :
    outputMean (SamplerWrapperPolicies.nonzeroProgram s) (fun r => test r.1) =
      (lambda ^ 3 + (1 - (modulus ^ 4 : Nat) * lambda) * retrySum 3) *
          test (.error .challengeExhausted) +
        lambda * retrySum 3 * successfulSum test := by
  change outputMean
      (BoundedSamplerWrapper.program nonzeroAccept Error.challengeExhausted
        Error.challengeExhausted 3 s) (fun r => test r.1) = _
  simpa only [expected] using nonzero_observation_law test 3 s

#print axioms encode_zeroTuple
#print axioms encodeTuple_zero_iff
#print axioms stage_sum
#print axioms zeroTuple
#print axioms zeroRaw
#print axioms successfulSum
#print axioms expected
#print axioms nonzero_observation_law
#print axioms nonzeroProgram_observation_law

end
end AspisV8R19.R938NonzeroObservationLaw
