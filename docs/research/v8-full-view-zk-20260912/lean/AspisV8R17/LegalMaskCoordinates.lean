import AspisV8R16.BalancedTransport

/-! Free coordinates for the actual one-pivot inactive balancing shape.
Active coordinates are retained, not added to the balancing equation. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
open AspisV8R16
noncomputable section
variable {I F : Type*} [DecidableEq I] [AddCommGroup F]

def fillFreeMask (pivot : I) (free : {i : I // i ≠ pivot} → F) (i : I) : F :=
  if h : i ≠ pivot then free ⟨i,h⟩ else 0

theorem balance_congr_off_pivot (inactive : Finset I) (pivot : I) (u v : I → F)
    (same : ∀ i, i ≠ pivot → u i = v i) :
    balance inactive pivot u = balance inactive pivot v := by
  have sums : ∑ i ∈ inactive.erase pivot, u i = ∑ i ∈ inactive.erase pivot, v i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact same i (Finset.mem_erase.mp hi).1
  funext i
  by_cases h : i=pivot
  · simp [balance, h, sums]
  · simp [balance, h, same i h]

theorem balance_fixed_on_legal (inactive : Finset I) (pivot : I) (hp : pivot ∈ inactive)
    (u : I → F) (legal : ∑ i ∈ inactive, u i = 0) : balance inactive pivot u = u := by
  rw [← Finset.sum_erase_add inactive u hp] at legal
  have pivot_value : -(∑ i ∈ inactive.erase pivot, u i) = u pivot := by
    have h := congrArg (fun x : F => x - ∑ i ∈ inactive.erase pivot, u i) legal
    simpa [add_comm] using h.symm
  funext i
  by_cases h : i=pivot
  · simp [balance, h, pivot_value]
  · simp [balance, h]

def legalMaskEquiv (inactive : Finset I) (pivot : I) (hp : pivot ∈ inactive) :
    ({i : I // i ≠ pivot} → F) ≃ {u : I → F // ∑ i ∈ inactive, u i = 0} where
  toFun free := ⟨balance inactive pivot (fillFreeMask pivot free),
    balance_sum_zero inactive pivot hp _⟩
  invFun u := fun i => u.val i.val
  left_inv free := by
    funext i
    simp [balance, fillFreeMask, i.property]
  right_inv u := by
    apply Subtype.ext
    calc
      balance inactive pivot (fillFreeMask pivot (fun i => u.val i.val)) =
          balance inactive pivot u.val := by
        apply balance_congr_off_pivot
        intro i hi
        simp [fillFreeMask, hi]
      _ = u.val := balance_fixed_on_legal inactive pivot hp u.val u.property

theorem legalMaskEquiv_preserves_free (inactive : Finset I) (pivot : I)
    (hp : pivot ∈ inactive) (free : {i : I // i ≠ pivot} → F) (i : I) (hi : i ≠ pivot) :
    (legalMaskEquiv inactive pivot hp free).val i = free ⟨i,hi⟩ := by
  simp [legalMaskEquiv, balance, fillFreeMask, hi]

/-- The source may draw a pivot value and overwrite it. Its value cannot
affect the final balanced vector; all other already-used coins are retained. -/
theorem balance_ignores_overwritten_draw (inactive : Finset I) (pivot : I)
    (u : I → F) (a : F) :
    balance inactive pivot (Function.update u pivot a) = balance inactive pivot u := by
  apply balance_congr_off_pivot
  intro i hi
  exact Function.update_of_ne hi a u

#print axioms balance_congr_off_pivot
#print axioms balance_fixed_on_legal
#print axioms legalMaskEquiv
#print axioms legalMaskEquiv_preserves_free
#print axioms balance_ignores_overwritten_draw
end
end AspisV8R17
