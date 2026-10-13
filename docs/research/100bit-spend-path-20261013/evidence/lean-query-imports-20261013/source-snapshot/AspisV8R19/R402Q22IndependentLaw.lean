import AspisV8R19.AdaptiveFirstReadLaw
import AspisV8R19.Q22SamplerProgram

/-! State irrelevance of the complete bounded q22 result kernel in the
independent-answer interpreter. Errors and stopping remain in the result.
This does not assert source/shared-oracle freshness or uniform query tuples. -/
set_option autoImplicit false
namespace AspisV8R19.R402Q22IndependentLaw
open DuplexFrames SourceDuplexStep SourceOraclePrograms Q22WordScan
open MemoizedProgramLaw OracleProgramOps AdaptiveFirstReadLaw
open AspisV8PairedCommitment
noncomputable section

theorem loop_state_irrelevance (n : Nat) (q : ScanState) (s s' : State)
    (test : Except Nat (List Nat) → ℚ) :
    independentMean (Q22SamplerProgram.loopProgram n s q) (fun view => test view.2.1) =
      independentMean (Q22SamplerProgram.loopProgram n s' q) (fun view => test view.2.1) := by
  cases n with
  | zero => rfl
  | succ n =>
      by_cases hd : q.draws < 64
      · simp only [Q22SamplerProgram.loopProgram, if_pos hd,
          independentMean_bind, squeezeProgram, independentMean]
      · simp only [Q22SamplerProgram.loopProgram, if_neg hd, independentMean]

theorem challenge_state_irrelevance (s s' : State)
    (test : Except Nat (List Nat) → ℚ) :
    independentMean (Q22SamplerProgram.challengeProgram s) (fun view => test view.2.1) =
      independentMean (Q22SamplerProgram.challengeProgram s') (fun view => test view.2.1) :=
  loop_state_irrelevance 8 ⟨[],0⟩ s s' test

theorem fresh_table_kernel (s s' : State)
    (t t' : Table Bytes State)
    (fresh : FreshFrom (Q22SamplerProgram.challengeProgram s) t)
    (fresh' : FreshFrom (Q22SamplerProgram.challengeProgram s') t')
    (test : Except Nat (List Nat) → ℚ) :
    lazyMean (Q22SamplerProgram.challengeProgram s) t (fun view => test view.2.1) =
      lazyMean (Q22SamplerProgram.challengeProgram s') t' (fun view => test view.2.1) := by
  rw [lazyMean_eq_independentMean _ _ fresh,
    lazyMean_eq_independentMean _ _ fresh']
  exact challenge_state_irrelevance s s' test

#print axioms loop_state_irrelevance
#print axioms challenge_state_irrelevance
#print axioms fresh_table_kernel
end
end AspisV8R19.R402Q22IndependentLaw
