import AspisV8R19.R413GuardedOracleDistance
import AspisV8R19.R407Q22CandidateKernel

/-! Complete bounded q22 result law compared to the uniform-candidate kernel,
with explicit cache-hit mass. No whole-program FreshFrom premise or numerical
bound for the source experiment, prefix, adversary, or retries is asserted. -/
set_option autoImplicit false
namespace AspisV8R19.R414Q22CacheHitDistance
open DuplexFrames SourceDuplexStep Q22WordScan Q22SamplerProgram
open MemoizedProgramLaw AdaptiveFirstReadLaw GuardedFirstRead
open R407Q22CandidateKernel AspisV8PairedCommitment
noncomputable section

def hitMass (n : Nat) (s : State) (q : ScanState) (t : Table Bytes State) : ℚ :=
  independentMean (guardFresh (loopProgram n s q) t)
    (fun v => if v.2 = none then 1 else 0)

theorem loop_distance (n : Nat) (s : State) (q : ScanState)
    (t : Table Bytes State) (test : Except Nat (List Nat) → ℚ)
    (bounded : ∀ r, 0 ≤ test r ∧ test r ≤ 1) :
    |lazyMean (loopProgram n s q) t (fun v => test v.2.1) -
      candidateKernel n q test| ≤ hitMass n s q t := by
  rw [← loop_candidate_kernel n s q test]
  exact R413GuardedOracleDistance.guarded_distance (loopProgram n s q) t _
    (fun v => bounded v.2.1)

theorem challenge_distance (s : State) (t : Table Bytes State)
    (test : Except Nat (List Nat) → ℚ) (bounded : ∀ r, 0 ≤ test r ∧ test r ≤ 1) :
    |lazyMean (challengeProgram s) t (fun v => test v.2.1) -
      candidateKernel 8 ⟨[],0⟩ test| ≤ hitMass 8 s ⟨[],0⟩ t :=
  loop_distance 8 s ⟨[],0⟩ t test bounded

#print axioms loop_distance
#print axioms challenge_distance
end
end AspisV8R19.R414Q22CacheHitDistance
