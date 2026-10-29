import R0Z.StatisticalDistance

/-! Transport equal finite laws through arbitrary observations and independent
finite coins. Output types need not be finite. All sums are symbolic. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.LawTransport

theorem mean_eq_sum_law {R V : Type} [Fintype R] (f : R → V) (test : V → ℚ)
    (s : Finset V) (hs : ∀ r, f r ∈ s) :
    mean (fun r => test (f r)) = ∑ v ∈ s, law f v * test v := by
  classical
  have hex (r : R) : test (f r) = ∑ v ∈ s, if f r = v then test v else 0 := by
    simp only [eq_comm (a := f r)]
    simp [hs r]
  simp only [mean, law, hex, div_mul_eq_mul_div, Finset.sum_mul,
    ite_mul, one_mul, zero_mul, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem mean_eq_of_equalLaws {R S V : Type} [Fintype R] [Fintype S]
    (f : R → V) (g : S → V) (test : V → ℚ) (h : EqualLaws f g) :
    mean (fun r => test (f r)) = mean (fun s => test (g s)) := by
  classical
  let s := support f ∪ support g
  have hf : ∀ r, f r ∈ s := fun r =>
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
  have hg : ∀ r, g r ∈ s := fun r =>
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
  rw [mean_eq_sum_law f test s hf, mean_eq_sum_law g test s hg]
  exact Finset.sum_congr rfl (fun v _ => congrArg (fun p => p * test v) (h v))

theorem mean_product {C R : Type} [Fintype C] [Fintype R] (f : C × R → ℚ) :
    mean f = mean (fun c => mean (fun r => f (c,r))) := by
  simp only [mean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  rw [← Finset.sum_div]
  ring

#print axioms mean_eq_of_equalLaws
#print axioms mean_product
end R0Z.LawTransport
