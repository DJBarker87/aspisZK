import GSInterpolationRowBasis
import GSInterpolationBudget

/-! Symbolic sizes; never reduce the six-million-entry basis to compute size. -/
set_option autoImplicit false
namespace AspisR1.GSProtocolBasisSizesM10
open AspisWide.GSInterpolationRowBasis AspisWide.GSInterpolationBudget

theorem initial : (basis 1024 114689 112).size = 6480098 := by
  rw [basis_size, rowCount_eq_weightedMonomialCount _ _ _ (by omega)]
  exact initial_weighted_count

theorem final : (basis 255 28673 112).size = 1626522 := by
  rw [basis_size, rowCount_eq_weightedMonomialCount _ _ _ (by omega)]
  exact final_weighted_count

#print axioms initial
#print axioms final
end AspisR1.GSProtocolBasisSizesM10
