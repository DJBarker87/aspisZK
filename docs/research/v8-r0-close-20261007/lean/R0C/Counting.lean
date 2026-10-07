import FS2.Statement

/-! Finite counting over abstract types. Never unfold a concrete byte-state
universe in a term to be unified. -/
set_option autoImplicit false
namespace R0C.Counting
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type} [Fintype A] [Fintype B]

theorem mean_indicator_card (p : A → Prop) :
    mean (fun a => indicator (p a)) =
      (Fintype.card {a // p a} : ℚ) / Fintype.card A := by
  simp only [mean, indicator, Finset.sum_boole, Fintype.card_subtype]

theorem point_mass_sum [Nonempty A] (f : A → B) :
    (∑ b, mean (fun a => indicator (f a = b))) = 1 := by
  classical
  simp only [mean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [indicator]
  simp

theorem uniform_of_point_mass_le [Nonempty A] [Nonempty B] (f : A → B)
    (h : ∀ b, mean (fun a => indicator (f a = b)) ≤ 1 / (Fintype.card B : ℚ)) :
    ∀ b, mean (fun a => indicator (f a = b)) = 1 / (Fintype.card B : ℚ) := by
  have hc : (Fintype.card B : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (∑ b, mean (fun a => indicator (f a = b))) =
      ∑ _b : B, (1 / (Fintype.card B : ℚ)) := by
    rw [point_mass_sum]
    simp [hc]
  exact fun b => (Finset.sum_eq_sum_iff_of_le (fun b _ => h b)).mp he b (Finset.mem_univ b)

/-- A total deterministic map with ideal point-mass upper bounds forces the
output cardinality to divide the input cardinality. -/
theorem card_dvd_of_point_mass_le [Nonempty A] [Nonempty B] (f : A → B)
    (h : ∀ b, mean (fun a => indicator (f a = b)) ≤ 1 / (Fintype.card B : ℚ)) :
    Fintype.card B ∣ Fintype.card A := by
  classical
  let b : B := Classical.arbitrary B
  have he := uniform_of_point_mass_le f h b
  rw [mean_indicator_card] at he
  have ha : (Fintype.card A : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card B : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm : (Fintype.card A : ℚ) =
      (Fintype.card B : ℚ) * (Fintype.card {a // f a = b} : ℚ) := by
    have hcross := (div_eq_div_iff ha hb).mp he
    linarith
  refine ⟨Fintype.card {a // f a = b}, ?_⟩
  exact_mod_cast hm

/-- Adding one exceptional output increases an ideal uniform-event bound by
at most one atom. This is about the ideal finite law, not a byte sampler. -/
theorem mean_or_eq_le [Nonempty A] (p : A → Prop) (a0 : A) :
    mean (fun a => indicator (p a ∨ a = a0)) ≤
      (Fintype.card {a // p a} + 1 : ℚ) / Fintype.card A := by
  classical
  rw [mean_indicator_card, Fintype.card_subtype, Fintype.card_subtype]
  have hset : (Finset.univ.filter fun a => p a ∨ a = a0) =
      (Finset.univ.filter p) ∪ {a0} := by ext a; simp [or_comm]
  rw [hset]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_union_le (Finset.univ.filter p) {a0}).trans (by simp)

#print axioms mean_indicator_card
#print axioms uniform_of_point_mass_le
#print axioms card_dvd_of_point_mass_le
#print axioms mean_or_eq_le
end
end R0C.Counting
