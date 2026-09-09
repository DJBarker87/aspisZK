import Mathlib.Data.Fintype.Fin

namespace AspisV8.EarlyC1Projection
theorem c1_margin : Fintype.card (Fin 262144) + 256 < 2 * 245609 := by
  rw [Fintype.card_fin]
  omega
#print axioms c1_margin
end AspisV8.EarlyC1Projection
