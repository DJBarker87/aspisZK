import GSConcreteRootRecovery

set_option autoImplicit false
noncomputable section
namespace AspisR1.GSConcreteRecoveryBudget
open AspisR1.GSConcreteRootRecovery AspisR1.CompPolyFactorMeanTools
open AspisV8R19.OracleResampling AspisV8PairedCommitment

/-- Even 31 calls at the larger of the actual two recovery bounds fit below
2^-127. The full caller must separately establish call count and fresh tapes. -/
theorem thirty_one_max_calls_small :
    (31 : ℚ) * (1025 * 112 * (1/2 : ℚ)^149) < (1/2 : ℚ)^127 := by
  norm_num

theorem max_call_budget :
    (1025 : ℚ) * 112 * (1/2 : ℚ)^149 < (1/2 : ℚ)^120 / 31 := by
  norm_num

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem initial_abort_budget (q : Nat) (points : Array (K × K))
    (hs : points.size = 1048576) (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    mean (fun H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin 149 → K × K =>
      abortIndicator (initial q 149 points hs H)) < (1/2 : ℚ)^120 / 31 := by
  exact lt_of_le_of_lt (initial_abort_le q 149 points hs hq hodd) max_call_budget

theorem final_abort_budget (q : Nat) (points : Array (K × K))
    (hs : points.size = 262144) (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    mean (fun H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin 149 → K × K =>
      abortIndicator (final q 149 points hs H)) < (1/2 : ℚ)^120 / 31 := by
  apply lt_of_le_of_lt (final_abort_le q 149 points hs hq hodd)
  calc
    (256 : ℚ) * 112 * (1/2 : ℚ)^149 ≤ 1025 * 112 * (1/2 : ℚ)^149 := by norm_num
    _ < (1/2 : ℚ)^120 / 31 := max_call_budget

#print axioms thirty_one_max_calls_small
#print axioms max_call_budget
#print axioms initial_abort_budget
#print axioms final_abort_budget
end AspisR1.GSConcreteRecoveryBudget
end
