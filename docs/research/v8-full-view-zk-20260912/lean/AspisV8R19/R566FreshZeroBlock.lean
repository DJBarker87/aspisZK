import AspisV8R19.SourceOraclePrograms
import AspisV8R19.R551FirstFourZeroBlockV10
import Mathlib.Tactic

set_option autoImplicit false

namespace AspisV8R19.R566FreshZeroBlock
open MemoizedProgramLaw OracleResampling SourceOraclePrograms
open DuplexFrames SourceDuplexStep
open AspisV8R19.R551FirstFourZeroBlockV10
open AspisV8PairedCommitment
noncomputable section

theorem fresh_squeeze_first_four_zero_law
    (s : State) (t : Table Bytes State)
    (hs : t (squeeze (bytes s)) = none) :
    lazyMean (squeezeProgram s) t
      (fun v => indicator (firstFourZero v.2.1)) =
      (1 / (modulus : ℚ)) ^ 4 := by
  rw [squeezeProgram, lazyMean, hs]
  simp only []
  rw [← firstFourZero_mean]
  apply mean_congr
  intro block
  cases ha : AspisV8PairedCommitment.put t (squeeze (bytes s)) block
      (advance (bytes s)) with
  | none =>
      simp only [lazyMean, ha]
      rw [mean_const]
  | some next =>
      simp only [lazyMean, ha]

#print axioms fresh_squeeze_first_four_zero_law
end
end AspisV8R19.R566FreshZeroBlock
