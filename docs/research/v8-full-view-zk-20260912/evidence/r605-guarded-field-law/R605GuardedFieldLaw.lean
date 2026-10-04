import AspisV8R19.R601ExactFieldMass
import AspisV8R19.R413GuardedOracleDistance

set_option autoImplicit false
namespace AspisV8R19.R605GuardedFieldLaw
open MemoizedProgramLaw OracleResampling AdaptiveFirstReadLaw GuardedFirstRead
open R601ExactFieldMass R584IndependentBlockSampler
open DuplexFrames SourceDuplexStep QM31SamplerProgram
open AspisV8R15.ExactTowerBase AspisV8PairedCommitment
noncomputable section

theorem cached_field_mass_distance (s : State) (q : QM31Exact)
    (cache : Table Bytes State) :
    |lazyMean (challengeProgram s) cache (fun v => fieldEvent q v.2.1) -
      ((1-(1/(2147483648 : ℚ))^8)/2147483647)^4| ≤
      independentMean (guardFresh (challengeProgram s) cache)
        (fun v => if v.2 = none then 1 else 0) := by
  have hb : ∀ v : View Bytes State (Option (List Nat) × State),
      0 ≤ fieldEvent q v.2.1 ∧ fieldEvent q v.2.1 ≤ 1 := by
    intro v
    unfold fieldEvent
    split <;> norm_num
  have h := R413GuardedOracleDistance.guarded_distance
    (challengeProgram s) cache (fun v => fieldEvent q v.2.1) hb
  have hm := source_independent_field_mass s q
  unfold outputMean at hm
  rw [hm] at h
  exact h

#print axioms cached_field_mass_distance
end
end AspisV8R19.R605GuardedFieldLaw
