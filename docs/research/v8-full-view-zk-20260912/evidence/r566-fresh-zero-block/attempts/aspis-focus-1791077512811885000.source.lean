import AspisV8R19.SourceOraclePrograms
import AspisV8R19.R551FirstFourZeroBlockV10
import Mathlib.Tactic

set_option autoImplicit false

namespace AspisV8R19.R566FreshZeroBlock
open MemoizedProgramLaw OracleResampling SourceOraclePrograms
open DuplexFrames SourceDuplexStep
open AspisV8R19.R551FirstFourZeroBlockV10
noncomputable section

theorem fresh_squeeze_first_four_zero_law
    (s : State) (t : Table Bytes State)
    (hs : t (squeeze (bytes s)) = none) :
    lazyMean (squeezeProgram s) t
      (fun v => indicator (firstFourZero v.2.1)) =
      (1 / (modulus : ℚ)) ^ 4 := by
  rw [squeezeProgram, lazyMean, hs]
  apply mean_congr
  intro block
  let t' := AspisV8PairedCommitment.put t (squeeze (bytes s)) block
  by_cases ha : t' (advance (bytes s)) = none
  · rw [lazyMean, ha]
    change mean (fun next : State =>
      indicator (firstFourZero block)) = _
    rw [mean_const]
    exact firstFourZero_mean
  · have hsome : ∃ next, t' (advance (bytes s)) = some next := by
      cases h : t' (advance (bytes s)) with
      | none => exact (ha h).elim
      | some next => exact ⟨next,h⟩
    rcases hsome with ⟨next,hn⟩
    rw [lazyMean, hn]
    change indicator (firstFourZero block) = _
    exact firstFourZero_mean

#print axioms fresh_squeeze_first_four_zero_law
end
end AspisV8R19.R566FreshZeroBlock
