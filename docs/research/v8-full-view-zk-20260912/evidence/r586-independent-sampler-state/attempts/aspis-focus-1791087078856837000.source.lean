import AspisV8R19.AdaptiveFirstReadLaw
import AspisV8R19.QM31SamplerProgram

set_option autoImplicit false
namespace AspisV8R19.R586IndependentSamplerState
open QM31SamplerProgram SourceOraclePrograms SamplerWords
open MemoizedProgramLaw OracleProgramOps AdaptiveFirstReadLaw OracleResampling
open DuplexFrames SourceDuplexStep

abbrev State := SourceDuplexStep.State
abbrev Bytes := DuplexFrames.Bytes

/-- Under the independent program interpreter, changing only the starting
transcript state cannot change a limb observer which discards returned state
and the query trace. -/
theorem limb_independent_state (budget : Nat) (s s' b : State) (j : Fin 9)
    (f : Option Nat → State → Fin 9 → ℚ) :
    independentMean (limbProgram budget ⟨s,b,j⟩)
      (fun v => f v.2.1 v.2.2.block v.2.2.index) =
    independentMean (limbProgram budget ⟨s',b,j⟩)
      (fun v => f v.2.1 v.2.2.block v.2.2.index) := by
  induction budget generalizing s s' b j f with
  | zero => rfl
  | succ budget ih =>
      by_cases hj : j.val = 8
      · simp only [limbProgram, readProgram, hj, ↓reduceDIte]
        repeat' rw [independentMean_bind]
        simp only [SourceOraclePrograms.squeezeProgram, independentMean]
      · have hjlt : j.val < 8 := by omega
        let i : Fin 8 := ⟨j.val,hjlt⟩
        let j' : Fin 9 := ⟨j.val+1, by have := j.isLt; omega⟩
        simp only [limbProgram, readProgram, hj, ↓reduceDIte, independentMean]
        by_cases hreject : masked 31 (word b i) = 2147483647
        · simpa [hreject, i, j'] using ih s s' b j' f
        · simp [hreject, i, j']

#print axioms limb_independent_state
end AspisV8R19.R586IndependentSamplerState
