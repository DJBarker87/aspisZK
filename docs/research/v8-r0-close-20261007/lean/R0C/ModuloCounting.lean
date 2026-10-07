import R0C.Counting

/-! Balanced reduction bounds, proved before any concrete byte/field instance.
The input and output encodings are equivalences, not distribution hypotheses.
No existing sampler law or Fiat-Shamir interface is redefined here. -/
set_option autoImplicit false
namespace R0C.ModuloCounting
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def reduce {B n : Nat} (hn : 0 < n) (x : Fin B) : Fin n :=
  ⟨x.val % n, Nat.mod_lt _ hn⟩

/-- A residue fiber injects into the possible quotient values. -/
theorem fiber_card_le (B n : Nat) (hn : 0 < n) (y : Fin n) :
    Fintype.card {x : Fin B // reduce hn x = y} ≤ B / n + 1 := by
  let f : {x : Fin B // reduce hn x = y} → Fin (B / n + 1) :=
    fun x => ⟨x.val.val / n, Nat.lt_succ_of_le
      (Nat.div_le_div_right (Nat.le_of_lt x.val.isLt))⟩
  have hf : Function.Injective f := by
    intro x z h
    apply Subtype.ext
    apply Fin.ext
    have hd : x.val.val / n = z.val.val / n := congrArg Fin.val h
    have hx : x.val.val % n = y.val := congrArg Fin.val x.property
    have hz : z.val.val % n = y.val := congrArg Fin.val z.property
    calc
      x.val.val = x.val.val % n + n * (x.val.val / n) := (Nat.mod_add_div _ _).symm
      _ = z.val.val % n + n * (z.val.val / n) := by rw [hx, hz, hd]
      _ = z.val.val := Nat.mod_add_div _ _
  simpa using Fintype.card_le_of_injective f hf

/-- Changing either encoding preserves the fiber count. -/
theorem encoded_mass_le {A E : Type} [Fintype A] [Fintype E]
    {B n : Nat} (hn : 0 < n)
    (input : A ≃ Fin B) (output : Fin n ≃ E) (y : E) :
    mean (fun a => indicator (output (reduce hn (input a)) = y)) ≤
      ((B / n + 1 : Nat) : ℚ) / B := by
  rw [Counting.mean_indicator_card]
  have hc : Fintype.card A = B := (Fintype.card_congr input).trans (Fintype.card_fin B)
  rw [hc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have he : {a : A // output (reduce hn (input a)) = y} ≃
      {x : Fin B // reduce hn x = output.symm y} :=
    input.subtypeEquiv (fun a => output.apply_eq_iff_eq_symm_apply)
  have h := (Fintype.card_congr he).le.trans (fiber_card_le B n hn (output.symm y))
  exact_mod_cast h

theorem quotient_bound (B n : Nat) (hB : 0 < B) (hn : 0 < n) :
    ((B / n + 1 : Nat) : ℚ) / B ≤ 1 / (n : ℚ) + 1 / (B : ℚ) := by
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hd : (B / n : Nat) * n ≤ B := Nat.div_mul_le_self B n
  have hdq : (B / n : Nat) * (n : ℚ) ≤ B := by exact_mod_cast hd
  rw [Nat.cast_add, Nat.cast_one]
  apply (div_le_iff₀ hBq).mpr
  apply (mul_le_mul_iff_left₀ hnq).mp
  field_simp
  nlinarith

theorem encoded_mass_slack {A E : Type} [Fintype A] [Fintype E]
    {B n : Nat} (hB : 0 < B) (hn : 0 < n)
    (input : A ≃ Fin B) (output : Fin n ≃ E) (y : E) :
    mean (fun a => indicator (output (reduce hn (input a)) = y)) ≤
      1 / (n : ℚ) + 1 / (B : ℚ) :=
  (encoded_mass_le hn input output y).trans (quotient_bound B n hB hn)

/-- Event bounds are obtained by summing atom bounds, with no independence
assumption between the output coordinates. -/
theorem event_mass_le {A E : Type} [Fintype A] [Fintype E]
    (f : A → E) (c : ℚ) (h : ∀ y, mean (fun a => indicator (f a = y)) ≤ c)
    (bad : Finset E) :
    mean (fun a => indicator (f a ∈ bad)) ≤ bad.card * c := by
  classical
  have he (a : A) : indicator (f a ∈ bad) = ∑ y ∈ bad, indicator (f a = y) := by
    simp [indicator, eq_comm]
  simp_rw [he]
  simp only [mean]
  rw [Finset.sum_comm]
  calc
    _ = ∑ y ∈ bad, mean (fun a => indicator (f a = y)) := by simp only [mean, Finset.sum_div]
    _ ≤ ∑ _y ∈ bad, c := Finset.sum_le_sum (fun y _ => h y)
    _ = bad.card * c := by simp

#print axioms fiber_card_le
#print axioms encoded_mass_slack
#print axioms event_mass_le
end
end R0C.ModuloCounting
