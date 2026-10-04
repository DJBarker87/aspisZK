import AspisV8R19.R609CircleRetryLaw
import AspisV8R19.R413GuardedOracleDistance

set_option autoImplicit false
namespace AspisV8R19.R612GuardedCircleLaw
open MemoizedProgramLaw OracleResampling AdaptiveFirstReadLaw GuardedFirstRead
open R609CircleRetryLaw R584IndependentBlockSampler
open DuplexFrames SourceDuplexStep AspisV8PairedCommitment
open AspisV8R15.ExactTowerBase SamplerWrapperPolicies
open R445InitialBlockRejectionLaw (modulus)
noncomputable section

def repeatLoss (s : State) (cache : Table Bytes State) : ℚ :=
  independentMean (guardFresh (SamplerCirclePolicy.circleProgram s) cache)
    (fun v => if v.2 = none then 1 else 0)

theorem cached_point_mass_distance (s : State) (a : QM31Exact) (ha : a.im ≠ 0)
    (cache : Table Bytes State) :
    |lazyMean (SamplerCirclePolicy.circleProgram s) cache
        (fun v => successEvent a v.2.1) - lambda*(1+retry+retry^2)| ≤ repeatLoss s cache := by
  have hb : ∀ v : View Bytes State (Except Error (QM31Exact × QM31Exact) × State),
      0 ≤ successEvent a v.2.1 ∧ successEvent a v.2.1 ≤ 1 := by
    intro v
    unfold successEvent
    split <;> norm_num
  have h := R413GuardedOracleDistance.guarded_distance
    (SamplerCirclePolicy.circleProgram s) cache (fun v => successEvent a v.2.1) hb
  have hm := selected_three_attempt_point_mass s a ha
  unfold outputMean at hm
  rw [hm] at h
  exact h

theorem cached_outer_error_distance (s : State) (cache : Table Bytes State) :
    |lazyMean (SamplerCirclePolicy.circleProgram s) cache
        (fun v => errorEvent Error.parameterExhausted v.2.1) - retry^3| ≤ repeatLoss s cache := by
  have hb : ∀ v : View Bytes State (Except Error (QM31Exact × QM31Exact) × State),
      0 ≤ errorEvent Error.parameterExhausted v.2.1 ∧
        errorEvent Error.parameterExhausted v.2.1 ≤ 1 := by
    intro v
    unfold errorEvent
    split <;> norm_num
  have h := R413GuardedOracleDistance.guarded_distance
    (SamplerCirclePolicy.circleProgram s) cache
    (fun v => errorEvent Error.parameterExhausted v.2.1) hb
  have hm := (selected_three_attempt_errors s).1
  unfold outputMean at hm
  rw [hm] at h
  exact h

theorem cached_inner_error_distance (s : State) (cache : Table Bytes State) :
    |lazyMean (SamplerCirclePolicy.circleProgram s) cache
        (fun v => errorEvent Error.challengeExhausted v.2.1) -
      (1-(modulus^4 : ℕ)*lambda)*(1+retry+retry^2)| ≤ repeatLoss s cache := by
  have hb : ∀ v : View Bytes State (Except Error (QM31Exact × QM31Exact) × State),
      0 ≤ errorEvent Error.challengeExhausted v.2.1 ∧
        errorEvent Error.challengeExhausted v.2.1 ≤ 1 := by
    intro v
    unfold errorEvent
    split <;> norm_num
  have h := R413GuardedOracleDistance.guarded_distance
    (SamplerCirclePolicy.circleProgram s) cache
    (fun v => errorEvent Error.challengeExhausted v.2.1) hb
  have hm := (selected_three_attempt_errors s).2
  unfold outputMean at hm
  rw [hm] at h
  exact h

#print axioms cached_point_mass_distance
#print axioms cached_outer_error_distance
#print axioms cached_inner_error_distance
end
end AspisV8R19.R612GuardedCircleLaw
