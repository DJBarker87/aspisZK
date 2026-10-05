import AspisV8R19.R935OrdinaryObservationLaw
import AspisV8R19.R609CircleRetryLaw
import AspisV8R19.SamplerCirclePolicy

/-! Full-observer law for the bounded circle sampler.  The law keeps both
explicit wrapper errors and evaluates arbitrary signed rational observers. -/
set_option autoImplicit false
namespace AspisV8R19.R945CircleObservationLaw

open MemoizedProgramLaw OracleProgramOps OracleResampling
open AspisV8R15.ExactTowerBase R584IndependentBlockSampler
open R599CanonicalFieldTuple R609CircleRetryLaw R935OrdinaryObservationLaw
open R608CircleOutcomeEvents
open SourceDuplexStep BoundedSamplerWrapper SamplerCirclePolicy
open R445InitialBlockRejectionLaw (modulus)
open scoped BigOperators
noncomputable section

abbrev Tuple := R935OrdinaryObservationLaw.Tuple
abbrev Error := SamplerWrapperPolicies.Error

def acceptedObserver (test : Except Error (QM31Exact × QM31Exact) → ℚ)
    (x : Tuple) : ℚ :=
  match SamplerCirclePolicy.accept (R935OrdinaryObservationLaw.encodeTuple x) with
  | none => 0
  | some p => test (.ok p)

def acceptedObserverSum (test : Except Error (QM31Exact × QM31Exact) → ℚ) : ℚ :=
  ∑ x : Tuple, acceptedObserver test x

def expected (n : Nat)
    (test : Except Error (QM31Exact × QM31Exact) → ℚ) : ℚ :=
  R609CircleRetryLaw.retry ^ n * test (.error .parameterExhausted) +
    (1 - (modulus ^ 4 : Nat) * R609CircleRetryLaw.lambda) *
      R609CircleRetryLaw.retrySum n * test (.error .challengeExhausted) +
    R609CircleRetryLaw.lambda * R609CircleRetryLaw.retrySum n * acceptedObserverSum test

def successfulObserver (test : Except Error (QM31Exact × QM31Exact) → ℚ)
    (out : Option (List Nat)) : ℚ :=
  match out with
  | none => 0
  | some xs =>
      match SamplerCirclePolicy.accept xs with
      | none => 0
      | some p => test (.ok p)

private theorem successful_observer_mean
    (test : Except Error (QM31Exact × QM31Exact) → ℚ) (s : State) :
    outputMean (QM31SamplerProgram.challengeProgram s)
        (fun r => successfulObserver test r.1) =
      R609CircleRetryLaw.lambda * acceptedObserverSum test := by
  exact ordinary_observation_law_error_zero (successfulObserver test) s rfl

/-- Arbitrary signed-observer law for every retry cap and initial state. -/
theorem circle_observation_law
    (test : Except Error (QM31Exact × QM31Exact) → ℚ) :
    ∀ (n : Nat) (s : State),
      outputMean
        (BoundedSamplerWrapper.program SamplerCirclePolicy.accept
          Error.challengeExhausted Error.parameterExhausted n s)
        (fun r => test r.1) = expected n test := by
  intro n
  induction n with
  | zero =>
      intro s
      simp [BoundedSamplerWrapper.program, outputMean_done, expected,
        acceptedObserverSum, R609CircleRetryLaw.retrySum]
  | succ n ih =>
      intro s
      rw [BoundedSamplerWrapper.program, outputMean_bind]
      let tail := expected n test
      let stage : Option (List Nat) → ℚ := fun out =>
        R609CircleRetryLaw.missing out * test (.error .challengeExhausted) +
          successfulObserver test out + R609CircleRetryLaw.rejected out * tail
      have hcontinuation : ∀ r : Option (List Nat) × State,
          outputMean
            (match r.1 with
            | none => .done (.error Error.challengeExhausted, r.2)
            | some xs => match SamplerCirclePolicy.accept xs with
              | some y => .done (.ok y, r.2)
              | none => BoundedSamplerWrapper.program SamplerCirclePolicy.accept
                  Error.challengeExhausted Error.parameterExhausted n r.2)
            (fun v => test v.1) =
          R609CircleRetryLaw.missing r.1 * test (.error .challengeExhausted) +
            successfulObserver test r.1 + R609CircleRetryLaw.rejected r.1 * tail := by
        intro r
        rcases r with ⟨out, t⟩
        cases out with
        | none => simp [stage, outputMean_done, R609CircleRetryLaw.missing,
            R609CircleRetryLaw.rejected, successfulObserver]
        | some xs =>
            cases ha : SamplerCirclePolicy.accept xs with
            | none => simp [stage, ha, ih, tail, R609CircleRetryLaw.missing,
                R609CircleRetryLaw.rejected, successfulObserver]
            | some p => simp [stage, ha, outputMean_done,
                R609CircleRetryLaw.missing, R609CircleRetryLaw.rejected,
                successfulObserver]
      trans outputMean (QM31SamplerProgram.challengeProgram s) (fun r => stage r.1)
      · apply outputMean_congr
        intro r
        rcases r with ⟨out, t⟩
        cases out with
        | none => simpa only [outputMean_done] using hcontinuation (none, t)
        | some xs =>
            cases hc : SamplerCirclePolicy.accept xs <;>
              simpa only [hc, outputMean_done] using hcontinuation (some xs, t)
      calc
        outputMean (QM31SamplerProgram.challengeProgram s)
            (fun r => R609CircleRetryLaw.missing r.1 *
                test (.error .challengeExhausted) +
              successfulObserver test r.1 +
                R609CircleRetryLaw.rejected r.1 * expected n test) =
            outputMean (QM31SamplerProgram.challengeProgram s)
                (fun r => R609CircleRetryLaw.missing r.1) *
                test (.error .challengeExhausted) +
              outputMean (QM31SamplerProgram.challengeProgram s)
                (fun r => successfulObserver test r.1) +
              outputMean (QM31SamplerProgram.challengeProgram s)
                (fun r => R609CircleRetryLaw.rejected r.1) * expected n test := by
          rw [R609CircleRetryLaw.outputMean_add,
            R609CircleRetryLaw.outputMean_add,
            R609CircleRetryLaw.outputMean_mul,
            R609CircleRetryLaw.outputMean_mul]
        _ = (1 - (modulus ^ 4 : Nat) * R609CircleRetryLaw.lambda) *
                test (.error .challengeExhausted) +
              R609CircleRetryLaw.lambda * acceptedObserverSum test +
              R609CircleRetryLaw.retry * expected n test := by
          rw [R609CircleRetryLaw.independent_missing_mass,
            successful_observer_mean, R609CircleRetryLaw.independent_retry_mass]
        _ = expected (n + 1) test := by
          dsimp [expected]
          rw [R609CircleRetryLaw.retrySum, pow_succ]
          ring

/-- Direct specialization to the existing three-attempt circle program. -/
theorem circleProgram_observation_law
    (test : Except Error (QM31Exact × QM31Exact) → ℚ) (s : State) :
    outputMean (SamplerCirclePolicy.circleProgram s) (fun r => test r.1) =
      R609CircleRetryLaw.retry ^ 3 * test (.error .parameterExhausted) +
        (1 - (modulus ^ 4 : Nat) * R609CircleRetryLaw.lambda) *
          R609CircleRetryLaw.retrySum 3 * test (.error .challengeExhausted) +
        R609CircleRetryLaw.lambda * R609CircleRetryLaw.retrySum 3 *
          acceptedObserverSum test := by
  rw [SamplerCirclePolicy.circleProgram]
  exact circle_observation_law test 3 s

#print axioms acceptedObserver
#print axioms acceptedObserverSum
#print axioms expected
#print axioms successfulObserver
#print axioms successful_observer_mean
#print axioms circle_observation_law
#print axioms circleProgram_observation_law

end
end AspisV8R19.R945CircleObservationLaw
