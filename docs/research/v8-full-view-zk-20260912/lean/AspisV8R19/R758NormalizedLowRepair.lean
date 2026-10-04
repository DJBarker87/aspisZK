import AspisV8R19.R739AugmentedQuery256

namespace AspisV8R19.R758NormalizedLowRepair
open AspisV8R19.R739AugmentedQuery256
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- Exact normalized contraction, with every low-coordinate repair retained. -/
theorem normalized_weight (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) (w : Fin 256 → F) :
    (∑ i, normalized t ht noneOne d i * w i) =
      w d - ∑ j : Fin 23, low t ht noneOne d j * w ⟨j.val, by omega⟩ := by
  simp only [normalized, sub_mul, Finset.sum_sub_distrib]
  rw [extendLow_sum]
  simp

/-- The diagnostic difference is accompanied by the exact generic repair.
No constant-low premise is made. -/
theorem normalized_weight_repair (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) (w : Fin 256 → F) :
    (∑ i, normalized t ht noneOne d i * w i) =
      (w d - w 0) - ∑ j : Fin 23,
        low t ht noneOne d j * (w ⟨j.val, by omega⟩ - w 0) := by
  have hs : (∑ j : Fin 23, low t ht noneOne d j * (w ⟨j.val, by omega⟩ - w 0)) =
      (∑ j : Fin 23, low t ht noneOne d j * w ⟨j.val, by omega⟩) - w 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [low_sum_one, one_mul]
  rw [normalized_weight, hs]
  ring

#print axioms normalized_weight
#print axioms normalized_weight_repair
end
end AspisV8R19.R758NormalizedLowRepair
