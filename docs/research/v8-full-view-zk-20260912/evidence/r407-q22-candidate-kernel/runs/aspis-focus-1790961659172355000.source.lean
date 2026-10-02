import AspisV8R19.R406SamplerWordDistribution
import AspisV8R19.R402Q22IndependentLaw

/-! Exact bounded q22 result kernel under the independent-answer interpreter.
Every block has eight uniform 18-bit words; the source scan, stopping flag,
64-draw limit, and error count are retained. No shared-oracle law is asserted. -/
set_option autoImplicit false
namespace AspisV8R19.R407Q22CandidateKernel
open DuplexFrames SourceDuplexStep SourceOraclePrograms Q22WordScan SamplerWords
open MemoizedProgramLaw OracleProgramOps AdaptiveFirstReadLaw OracleResampling
noncomputable section

def candidateKernel : Nat → ScanState → (Except Nat (List Nat) → ℚ) → ℚ
  | 0,q,test => test (finish q)
  | n+1,q,test =>
      if q.draws < 64 then mean (fun candidates : Fin 8 → Fin (2^18) =>
        let r := scan q (List.ofFn (fun j => (candidates j).val))
        if r.2 then test (finish r.1) else candidateKernel n r.1 test)
      else test (finish q)

theorem loop_candidate_kernel (n : Nat) (s : State) (q : ScanState)
    (test : Except Nat (List Nat) → ℚ) :
    independentMean (Q22SamplerProgram.loopProgram n s q) (fun view => test view.2.1) =
      candidateKernel n q test := by
  induction n generalizing s q with
  | zero => rfl
  | succ n ih =>
      by_cases hd : q.draws < 64
      · simp only [Q22SamplerProgram.loopProgram, candidateKernel, if_pos hd,
          independentMean_bind, squeezeProgram, independentMean]
        rw [← R406SamplerWordDistribution.uniform_candidates (fun xs =>
          let r := scan q xs
          if r.2 then test (finish r.1) else candidateKernel n r.1 test)]
        apply mean_congr
        intro out
        by_cases hs : (scan q (words 18 out)).2 = true
        · simp only [hs, ↓reduceIte, independentMean]
          exact mean_const _
        · have hf : (scan q (words 18 out)).2 = false := by
            cases h : (scan q (words 18 out)).2 <;> simp_all
          simp only [hf, Bool.false_eq_true, ↓reduceIte]
          simp_rw [ih]
          exact mean_const _
      · simp only [Q22SamplerProgram.loopProgram, candidateKernel, if_neg hd,
          independentMean]

theorem challenge_candidate_kernel (s : State)
    (test : Except Nat (List Nat) → ℚ) :
    independentMean (Q22SamplerProgram.challengeProgram s) (fun view => test view.2.1) =
      candidateKernel 8 ⟨[],0⟩ test := loop_candidate_kernel 8 s ⟨[],0⟩ test

#print axioms loop_candidate_kernel
#print axioms challenge_candidate_kernel
end
end AspisV8R19.R407Q22CandidateKernel
