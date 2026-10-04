import AspisV8R19.R608CircleOutcomeEvents

set_option autoImplicit false
namespace AspisV8R19.R609CircleRetryLaw
open MemoizedProgramLaw OracleProgramOps OracleResampling AdaptiveFirstReadLaw
open R584IndependentBlockSampler R601ExactFieldMass R607FieldSetMass
open R599CanonicalFieldTuple
open R608CircleOutcomeEvents SourceDuplexStep BoundedSamplerWrapper
open SamplerWrapperPolicies AspisV8R15.ExactTowerBase
open R445InitialBlockRejectionLaw (modulus)
noncomputable section

def lambda : ℚ := ((1-(1/(2147483648 : ℚ))^8)/2147483647)^4
def retry : ℚ := (modulus^2 : ℕ) * lambda
def retrySum : Nat → ℚ
  | 0 => 0
  | n+1 => 1 + retry * retrySum n

theorem outputMean_add {I A O : Type} [Fintype A]
    (p : Program I A O) (f g : O → ℚ) :
    outputMean p (fun o => f o + g o) = outputMean p f + outputMean p g := by
  induction p with
  | done o => rfl
  | ask i next ih =>
      change mean (fun a => outputMean (next a) (fun o => f o + g o)) = _
      rw [mean_congr (fun a => ih a)]
      simp only [outputMean, independentMean, mean, Finset.sum_add_distrib, add_div]

theorem outputMean_mul {I A O : Type} [Fintype A]
    (p : Program I A O) (f : O → ℚ) (c : ℚ) :
    outputMean p (fun o => f o * c) = outputMean p f * c := by
  induction p with
  | done o => rfl
  | ask i next ih =>
      change mean (fun a => outputMean (next a) (fun o => f o * c)) = _
      rw [mean_congr (fun a => ih a)]
      simp only [outputMean, independentMean, mean]
      rw [← Finset.sum_mul]
      ring

theorem outputMean_const {I A O : Type} [Fintype A] [Nonempty A]
    (p : Program I A O) (c : ℚ) : outputMean p (fun _ => c) = c := by
  induction p with
  | done o => rfl
  | ask i next ih =>
      change mean (fun a => outputMean (next a) (fun _ => c)) = c
      rw [mean_congr (fun a => ih a), mean_const]

def missing (out : Option (List Nat)) : ℚ := if out = none then 1 else 0

theorem independent_missing_mass (s : State) :
    outputMean (QM31SamplerProgram.challengeProgram s) (fun r => missing r.1) =
      1 - (modulus^4 : ℕ) * lambda := by
  have hall (out : Option (List Nat)) :
      missing out + setEvent Finset.univ out = 1 := by
    cases out with
    | none => simp [missing, setEvent]
    | some xs =>
        have hex : ∃ x ∈ (Finset.univ : Finset Tuple),
            SamplerFieldDecode.decode xs = tupleField x := by
          exact ⟨tupleFieldEquiv.symm (SamplerFieldDecode.decode xs), Finset.mem_univ _,
            (tupleFieldEquiv.apply_symm_apply _).symm⟩
        simp [missing, setEvent, hex]
  have hsum := outputMean_congr (QM31SamplerProgram.challengeProgram s)
    (fun r => hall r.1)
  rw [outputMean_add, outputMean_const, source_independent_set_mass] at hsum
  have hc : (Finset.univ : Finset Tuple).card = modulus^4 := by simp [Tuple]
  rw [hc] at hsum
  change _ + (modulus^4 : ℕ) * lambda = 1 at hsum
  linarith

def rejected (out : Option (List Nat)) : ℚ :=
  if ∃ xs, out = some xs ∧ SamplerCirclePolicy.accept xs = none then 1 else 0

theorem independent_retry_mass (s : State) :
    outputMean (QM31SamplerProgram.challengeProgram s) (fun r => rejected r.1) = retry := by
  have he : (fun r : Option (List Nat) × State => rejected r.1) =
      (fun r => setEvent rejectedTuples r.1) := by
    funext r
    exact (rejected_event_eq r.1).symm
  rw [he, source_independent_set_mass, rejected_tuple_count]
  rfl

def successEvent (a : QM31Exact) (out : Except Error (QM31Exact × QM31Exact)) : ℚ :=
  if out = .ok (SamplerCirclePolicy.point a) then 1 else 0

theorem independent_point_mass (n : Nat) (s : State) (a : QM31Exact) (ha : a.im ≠ 0) :
    outputMean
      (program SamplerCirclePolicy.accept Error.challengeExhausted Error.parameterExhausted n s)
      (fun r => successEvent a r.1) = lambda * retrySum n := by
  induction n generalizing s with
  | zero => simp [program, outputMean_done, successEvent, retrySum]
  | succ n ih =>
      rw [program, outputMean_bind]
      have hobs (r : Option (List Nat) × State) :
          outputMean
            (match r.1 with
            | none => .done (.error Error.challengeExhausted,r.2)
            | some xs => match SamplerCirclePolicy.accept xs with
              | some y => .done (.ok y,r.2)
              | none => program SamplerCirclePolicy.accept Error.challengeExhausted
                  Error.parameterExhausted n r.2)
            (fun v => successEvent a v.1) =
          fieldEvent a r.1 + rejected r.1 * (lambda * retrySum n) := by
        rcases r with ⟨out,t⟩
        cases out with
        | none => simp [outputMean_done, successEvent, fieldEvent, rejected]
        | some xs =>
            cases hac : SamplerCirclePolicy.accept xs with
            | none =>
                have hne : SamplerFieldDecode.decode xs ≠ a := by
                  intro heq
                  have hp := (accept_point_iff xs a ha).mpr heq
                  rw [hac] at hp
                  cases hp
                simp [hac, ih, fieldEvent, rejected, hne]
            | some y =>
                have heq : y = SamplerCirclePolicy.point a ↔ SamplerFieldDecode.decode xs = a := by
                  simpa only [hac, Option.some.injEq] using accept_point_iff xs a ha
                simp [hac, outputMean_done, successEvent, fieldEvent, rejected, heq]
      rw [outputMean_congr (QM31SamplerProgram.challengeProgram s) hobs, outputMean_add, outputMean_mul,
        source_independent_field_mass, independent_retry_mass]
      change lambda + retry * (lambda * retrySum n) = lambda * retrySum (n+1)
      rw [retrySum]
      ring

theorem selected_three_attempt_point_mass (s : State) (a : QM31Exact) (ha : a.im ≠ 0) :
    outputMean (SamplerCirclePolicy.circleProgram s) (fun r => successEvent a r.1) =
      lambda * (1 + retry + retry^2) := by
  rw [SamplerCirclePolicy.circleProgram, independent_point_mass 3 s a ha]
  simp only [retrySum]
  ring

def errorEvent (e : Error) (out : Except Error (QM31Exact × QM31Exact)) : ℚ :=
  if out = .error e then 1 else 0

theorem independent_outer_error_mass (n : Nat) (s : State) :
    outputMean
      (program SamplerCirclePolicy.accept Error.challengeExhausted Error.parameterExhausted n s)
      (fun r => errorEvent Error.parameterExhausted r.1) = retry^n := by
  induction n generalizing s with
  | zero => simp [program, outputMean_done, errorEvent]
  | succ n ih =>
      rw [program, outputMean_bind]
      have hobs (r : Option (List Nat) × State) :
          outputMean
            (match r.1 with
            | none => .done (.error Error.challengeExhausted,r.2)
            | some xs => match SamplerCirclePolicy.accept xs with
              | some y => .done (.ok y,r.2)
              | none => program SamplerCirclePolicy.accept Error.challengeExhausted
                  Error.parameterExhausted n r.2)
            (fun v => errorEvent Error.parameterExhausted v.1) = rejected r.1 * retry^n := by
        rcases r with ⟨out,t⟩
        cases out with
        | none => simp [outputMean_done, errorEvent, rejected]
        | some xs =>
            cases hac : SamplerCirclePolicy.accept xs with
            | none => simp [hac, ih, rejected]
            | some y => simp [hac, outputMean_done, errorEvent, rejected]
      rw [outputMean_congr (QM31SamplerProgram.challengeProgram s) hobs, outputMean_mul, independent_retry_mass, pow_succ]
      ring

theorem independent_inner_error_mass (n : Nat) (s : State) :
    outputMean
      (program SamplerCirclePolicy.accept Error.challengeExhausted Error.parameterExhausted n s)
      (fun r => errorEvent Error.challengeExhausted r.1) =
      (1 - (modulus^4 : ℕ) * lambda) * retrySum n := by
  induction n generalizing s with
  | zero => simp [program, outputMean_done, errorEvent, retrySum]
  | succ n ih =>
      rw [program, outputMean_bind]
      have hobs (r : Option (List Nat) × State) :
          outputMean
            (match r.1 with
            | none => .done (.error Error.challengeExhausted,r.2)
            | some xs => match SamplerCirclePolicy.accept xs with
              | some y => .done (.ok y,r.2)
              | none => program SamplerCirclePolicy.accept Error.challengeExhausted
                  Error.parameterExhausted n r.2)
            (fun v => errorEvent Error.challengeExhausted v.1) =
          missing r.1 + rejected r.1 * ((1-(modulus^4 : ℕ)*lambda)*retrySum n) := by
        rcases r with ⟨out,t⟩
        cases out with
        | none => simp [outputMean_done, errorEvent, missing, rejected]
        | some xs =>
            cases hac : SamplerCirclePolicy.accept xs with
            | none => simp [hac, ih, missing, rejected]
            | some y => simp [hac, outputMean_done, errorEvent, missing, rejected]
      rw [outputMean_congr (QM31SamplerProgram.challengeProgram s) hobs, outputMean_add, outputMean_mul,
        independent_missing_mass, independent_retry_mass, retrySum]
      ring

theorem selected_three_attempt_errors (s : State) :
    outputMean (SamplerCirclePolicy.circleProgram s)
      (fun r => errorEvent Error.parameterExhausted r.1) = retry^3 ∧
    outputMean (SamplerCirclePolicy.circleProgram s)
      (fun r => errorEvent Error.challengeExhausted r.1) =
      (1-(modulus^4 : ℕ)*lambda)*(1+retry+retry^2) := by
  constructor
  · exact independent_outer_error_mass 3 s
  · rw [SamplerCirclePolicy.circleProgram, independent_inner_error_mass, retrySum,
      retrySum, retrySum, retrySum]
    ring

#print axioms outputMean_add
#print axioms outputMean_mul
#print axioms outputMean_const
#print axioms independent_missing_mass
#print axioms independent_retry_mass
#print axioms independent_point_mass
#print axioms selected_three_attempt_point_mass
#print axioms independent_outer_error_mass
#print axioms independent_inner_error_mass
#print axioms selected_three_attempt_errors
end
end AspisV8R19.R609CircleRetryLaw
