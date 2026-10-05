import AspisV8R19.R609CircleRetryLaw

set_option autoImplicit false
namespace AspisV8R19.R932NonzeroIndependentMass

open MemoizedProgramLaw OracleProgramOps
open R584IndependentBlockSampler R594JointChallengeMass R599CanonicalFieldTuple
open R609CircleRetryLaw
open SourceDuplexStep BoundedSamplerWrapper SamplerWrapperPolicies
open AspisV8R15.ExactTowerBase
open R445InitialBlockRejectionLaw (modulus)
noncomputable section

/-- The geometric sum for repeated rejection of the raw all-zero tuple. -/
def retrySum : Nat → ℚ
  | 0 => 0
  | n + 1 => 1 + lambda * retrySum n

def outputEvent (target : List Nat)
    (out : Except SamplerWrapperPolicies.Error (List Nat)) : ℚ :=
  if out = .ok target then 1 else 0

def exhaustionEvent
    (out : Except SamplerWrapperPolicies.Error (List Nat)) : ℚ :=
  if out = .error .challengeExhausted then 1 else 0

def rawZero (out : Option (List Nat)) : ℚ :=
  if out = some [0, 0, 0, 0] then 1 else 0

def missing (out : Option (List Nat)) : ℚ :=
  if out = none then 1 else 0

theorem independent_raw_zero_mass (s : SourceDuplexStep.State) :
    outputMean (QM31SamplerProgram.challengeProgram s)
      (fun r => rawZero r.1) = lambda := by
  have hzero :
      (List.ofFn (fun _ : Fin 4 => (0 : Fin modulus))).map Fin.val =
        [0, 0, 0, 0] := by
    rw [ofFn_four_values]
    simp
  have hevent : (fun r : Option (List Nat) × State => rawZero r.1) =
      (fun r => tupleEvent (fun _ => (0 : Fin modulus)) r.1) := by
    funext r
    cases r.1 <;> simp [rawZero, tupleEvent]
  rw [hevent, source_independent_tuple_mass s (fun _ => (0 : Fin modulus))]
  rfl

theorem independent_missing_mass (s : SourceDuplexStep.State) :
    outputMean (QM31SamplerProgram.challengeProgram s)
      (fun r => missing r.1) = 1 - (modulus ^ 4 : Nat) * lambda := by
  simpa [missing, R609CircleRetryLaw.missing, lambda] using
    R609CircleRetryLaw.independent_missing_mass s

theorem independent_output_mass (target : Fin 4 → Fin modulus)
    (htarget : (List.ofFn target).map Fin.val ≠ [0, 0, 0, 0])
    (n : Nat) (s : SourceDuplexStep.State) :
    outputMean
      (BoundedSamplerWrapper.program nonzeroAccept
        Error.challengeExhausted Error.challengeExhausted n s)
      (fun r => outputEvent ((List.ofFn target).map Fin.val) r.1) =
        lambda * retrySum n := by
  induction n generalizing s with
  | zero => simp [BoundedSamplerWrapper.program, outputMean_done,
      outputEvent, retrySum]
  | succ n ih =>
      rw [BoundedSamplerWrapper.program, outputMean_bind]
      have hterm (r : Option (List Nat) × State) :
          outputMean
            (match r.1 with
            | none => .done (.error Error.challengeExhausted, r.2)
            | some xs => match nonzeroAccept xs with
              | some y => .done (.ok y, r.2)
              | none => BoundedSamplerWrapper.program nonzeroAccept
                  Error.challengeExhausted Error.challengeExhausted n r.2)
            (fun v => outputEvent ((List.ofFn target).map Fin.val) v.1) =
          (if r.1 = some ((List.ofFn target).map Fin.val) then 1 else 0) +
            rawZero r.1 * (lambda * retrySum n) := by
        have htarget_nonzero_values :
            ¬ ((target 0).val = 0 ∧ (target 1).val = 0 ∧
              (target 2).val = 0 ∧ (target 3).val = 0) := by
          intro hv
          apply htarget
          rw [ofFn_four_values]
          simp [hv]
        rcases r with ⟨out, t⟩
        cases out with
        | none => simp [outputMean_done, outputEvent, rawZero]
        | some xs =>
            by_cases hz : xs = [0, 0, 0, 0]
            · subst xs
              have htarget' :
                  [(target 0).val, (target 1).val, (target 2).val, (target 3).val] ≠
                    [0, 0, 0, 0] := by
                simpa only [ofFn_four_values] using htarget
              simp only [nonzeroAccept, if_pos rfl]
              rw [ih t]
              simp [rawZero, outputEvent, htarget', htarget_nonzero_values]
            · by_cases ht : xs = (List.ofFn target).map Fin.val
              · subst xs
                have htarget' :
                    [(target 0).val, (target 1).val, (target 2).val, (target 3).val] ≠
                      [0, 0, 0, 0] := by
                  simpa only [ofFn_four_values] using htarget
                simp [nonzeroAccept, rawZero, outputEvent, htarget',
                  htarget_nonzero_values]
              · have ht' : ¬ xs =
                    [(target 0).val, (target 1).val, (target 2).val,
                      (target 3).val] := by
                simpa only [ofFn_four_values] using ht
                simp [nonzeroAccept, hz, rawZero, outputEvent, ht']
      trans outputMean (QM31SamplerProgram.challengeProgram s)
        (fun r => (if r.1 = some ((List.ofFn target).map Fin.val) then 1 else 0) +
          rawZero r.1 * (lambda * retrySum n))
      · apply outputMean_congr
        intro r
        simpa only [] using hterm r
      rw [outputMean_add, outputMean_mul]
      have htargetMass :
          outputMean (QM31SamplerProgram.challengeProgram s)
            (fun r => if r.1 = some ((List.ofFn target).map Fin.val) then 1 else 0) = lambda := by
        simpa [R594JointChallengeMass.tupleEvent, lambda] using
          source_independent_tuple_mass s target
      rw [htargetMass, independent_raw_zero_mass, retrySum]
      ring

theorem independent_exhaustion_mass (n : Nat) (s : SourceDuplexStep.State) :
    outputMean
      (BoundedSamplerWrapper.program nonzeroAccept
        Error.challengeExhausted Error.challengeExhausted n s)
      (fun r => exhaustionEvent r.1) =
        lambda ^ n + (1 - (modulus ^ 4 : Nat) * lambda) * retrySum n := by
  induction n generalizing s with
  | zero => simp [BoundedSamplerWrapper.program, outputMean_done,
      exhaustionEvent, retrySum]
  | succ n ih =>
      rw [BoundedSamplerWrapper.program, outputMean_bind]
      have hterm (r : Option (List Nat) × State) :
          outputMean
            (match r.1 with
            | none => .done (.error Error.challengeExhausted, r.2)
            | some xs => match nonzeroAccept xs with
              | some y => .done (.ok y, r.2)
              | none => BoundedSamplerWrapper.program nonzeroAccept
                  Error.challengeExhausted Error.challengeExhausted n r.2)
            (fun v => exhaustionEvent v.1) =
          missing r.1 + rawZero r.1 *
            (lambda ^ n + (1 - (modulus ^ 4 : Nat) * lambda) * retrySum n) := by
        rcases r with ⟨out, t⟩
        cases out with
        | none => simp [outputMean_done, exhaustionEvent, missing, rawZero]
        | some xs =>
            by_cases hz : xs = [0, 0, 0, 0]
            · subst xs
              simp only [nonzeroAccept, if_pos rfl]
              rw [ih t]
              simp [exhaustionEvent, missing, rawZero]
            · simp [nonzeroAccept, hz, exhaustionEvent, missing, rawZero,
                outputMean_done]
      trans outputMean (QM31SamplerProgram.challengeProgram s)
        (fun r => missing r.1 + rawZero r.1 *
          (lambda ^ n + (1 - (modulus ^ 4 : Nat) * lambda) * retrySum n))
      · apply outputMean_congr
        intro r
        simpa only [] using hterm r
      rw [outputMean_add, outputMean_mul, independent_missing_mass,
        independent_raw_zero_mass, retrySum, pow_succ]
      ring

theorem selected_three_attempt_nonzero (s : SourceDuplexStep.State)
    (target : Fin 4 → Fin modulus)
    (htarget : (List.ofFn target).map Fin.val ≠ [0, 0, 0, 0]) :
    outputMean (SamplerWrapperPolicies.nonzeroProgram s)
      (fun r => outputEvent ((List.ofFn target).map Fin.val) r.1) =
        lambda * (1 + lambda + lambda ^ 2) := by
  rw [SamplerWrapperPolicies.nonzeroProgram, independent_output_mass target htarget]
  simp only [retrySum]
  ring

theorem selected_three_attempt_exhaustion (s : SourceDuplexStep.State) :
    outputMean (SamplerWrapperPolicies.nonzeroProgram s)
      (fun r => exhaustionEvent r.1) =
        lambda ^ 3 + (1 - (modulus ^ 4 : Nat) * lambda) *
          (1 + lambda + lambda ^ 2) := by
  rw [SamplerWrapperPolicies.nonzeroProgram, independent_exhaustion_mass]
  simp only [retrySum]
  ring

#print axioms independent_raw_zero_mass
#print axioms independent_missing_mass
#print axioms independent_output_mass
#print axioms independent_exhaustion_mass
#print axioms selected_three_attempt_nonzero
#print axioms selected_three_attempt_exhaustion

end
end AspisV8R19.R932NonzeroIndependentMass
