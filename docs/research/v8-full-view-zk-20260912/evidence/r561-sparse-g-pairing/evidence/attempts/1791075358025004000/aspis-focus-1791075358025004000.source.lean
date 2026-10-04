import AspisV8R19.TwoSwapSourceG
import AspisV8R17.MaskSourceSlices

/-! Complete sparse-G scatter pairing in the exact field/table model.  This
is not a Rust scatter-execution refinement or a source-slice correspondence. -/
set_option autoImplicit false
namespace AspisV8R19.R561

open scoped BigOperators
open AspisV8R17
open AspisR19 TwoSwapSourceTable
open AspisR19.TwoSwapSourceG

noncomputable section
variable {F : Type*} [Field F]

private theorem original_eq_sumIndicators (weights : Fin 271 → F) (r : Fin 1024) :
    original weights r = ∑ i : Fin 271,
      if order (coinIndex i) = r then weights i else 0 := by
  classical
  by_cases hmem : ∃ i : Fin 271, order (coinIndex i) = r
  · rcases hmem with ⟨i, hi⟩
    subst r
    rw [original_at]
    symm
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hne : order (coinIndex j) ≠ order (coinIndex i) := by
        intro he
        apply hji
        exact coinIndex_injective (order.injective he)
      simp [hne]
    · simp
  · have hoff : ∀ i : Fin 271, order (coinIndex i) ≠ r := by
      intro i hi
      exact hmem ⟨i, hi⟩
    rw [show original weights r = 0 by
      unfold original
      apply SparseGScatter.updates_off
      intro i _ hi
      exact hoff i hi]
    simp [hoff]

/-- Every sparse G coin appears exactly once at `order (128 + 3*i)`. -/
theorem original_pairing (weights : Fin 271 → F) (m : Fin 1024 → F) :
    (∑ r : Fin 1024, original weights r * m r) =
      ∑ i : Fin 271, weights i * m (order (coinIndex i)) := by
  classical
  calc
    (∑ r : Fin 1024, original weights r * m r) =
        ∑ r : Fin 1024, (∑ i : Fin 271,
          if order (coinIndex i) = r then weights i else 0) * m r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [original_eq_sumIndicators]
    _ = ∑ r : Fin 1024, ∑ i : Fin 271,
          (if order (coinIndex i) = r then weights i else 0) * m r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_mul]
    _ = ∑ i : Fin 271, ∑ r : Fin 1024,
          (if order (coinIndex i) = r then weights i else 0) * m r := by
      exact Finset.sum_comm
    _ = ∑ i : Fin 271, weights i * m (order (coinIndex i)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_eq_single (order (coinIndex i))
      · intro r _ hr
        simp [hr]
      · simp

def sparseSlices (m : Fin 1024 → F) (j : ℕ) : F :=
  if h : j < 271 then m (order (coinIndex ⟨j, h⟩)) else 0

theorem sparseSlices_at (m : Fin 1024 → F) (i : Fin 271) :
    sparseSlices m i.val = m (order (coinIndex i)) := by
  simp [sparseSlices]

/-- The sparse source order gives the exact 271 inputs consumed by the
existing mask-weight dot product. -/
theorem maskWeights_sparse_pairing (half : F) (z : RoundCoins F 10)
    (m : Fin 1024 → F) :
    (∑ r : Fin 1024, original (maskWeights271 half z) r * m r) =
      sourceMaskLoop half (sparseSlices m 0)
        (literalMaskContributions 10
          (readRoundCoins 26 (sparseSlices m) 10 1) z) := by
  rw [original_pairing]
  have hread := maskCoins271_reads (sparseSlices m)
  calc
    (∑ i : Fin 271, maskWeights271 half z i * m (order (coinIndex i))) =
        ∑ i : Fin 271, maskWeights271 half z i *
          maskCoins271 (sparseSlices m 0)
            (readRoundCoins 26 (sparseSlices m) 10 1) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hread, sparseSlices_at]
    _ = sourceMaskLoop half (sparseSlices m 0)
          (literalMaskContributions 10
            (readRoundCoins 26 (sparseSlices m) 10 1) z) := by
      exact maskWeights271_dot half (sparseSlices m 0)
        (readRoundCoins 26 (sparseSlices m) 10 1) z

#print axioms original_pairing
#print axioms maskWeights_sparse_pairing
end
end AspisV8R19.R561
