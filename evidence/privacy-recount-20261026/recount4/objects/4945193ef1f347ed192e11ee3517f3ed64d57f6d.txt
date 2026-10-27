import R1Z.QueryScanRealLazyBound
import R1Z.QueryScanHistoryRealNumerics

set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanRealLazyJoin
open R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV R1Z.QueryScanHistorySplit
  R1Z.QueryScanPrivacyFinal R1Z.QueryScanRealLazyBound
attribute [local instance] Classical.propDecidable

/-- Aggregate model mass is transported once, with no per-attempt copy of κ. -/
theorem join_le {A M : Type} [Fintype A] [Fintype M]
    (f : A → ℚ) (g : M → ℚ) (bad : Fin 8 → M → Prop)
    (e : ModelExecutionJoin f g bad) (κ : ℚ)
    (hb : eventMass (fun m => ∃ i, bad i m) ≤ κ + 8 * scanProbability)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (hg : ∀ m, 0 ≤ g m ∧ g m ≤ 1) :
    |mean f - mean g| ≤ κ + 8 / (2 : ℚ)^486 := by
  have hm := e.cp.meanM (fun m => if ∃ i, bad i m then (1 : ℚ) else 0)
  have hmass : eventMass (fun s => ∃ i, bad i (e.cp.toM s)) =
      eventMass (fun m => ∃ i, bad i m) := by
    unfold eventMass
    convert hm using 1 <;> congr 1 <;> funext z <;> split_ifs <;> rfl
  rw [← e.cp.meanR f, ← e.cp.meanM g]
  have ht := until_bad _ _ (fun s => hf _) (fun s => hg _) _ e.agreement
  have h8 := mul_le_mul_of_nonneg_left scan_probability_le (by norm_num : (0 : ℚ) ≤ 8)
  calc _ ≤ eventMass (fun s => ∃ i, bad i (e.cp.toM s)) := ht
       _ = eventMass (fun m => ∃ i, bad i m) := hmass
       _ ≤ κ + 8 * scanProbability := hb
       _ ≤ κ + 8 / (2 : ℚ)^486 := by simpa only [mul_one_div] using add_le_add (le_refl κ) h8

theorem lazy_budget_mono {M Q : ℕ} (h : M ≤ Q) : lazyBudget M ≤ lazyBudget Q := by
  unfold lazyBudget
  gcongr

/-- Symbolic power splitting at the existing binary read-count envelope. -/
theorem lazy_budget_small {M : ℕ} (hM : M ≤ 2^25) :
    lazyBudget M ≤ 1 / (2 : ℚ)^109 := by
  apply (lazy_budget_mono hM).trans
  have hp : ((2^25 : ℕ) : ℚ) = (2 : ℚ)^25 := by norm_cast
  unfold lazyBudget
  rw [hp]
  have h25 : (2 : ℚ)^25 ≤ (2 : ℚ)^50 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hh : (2 : ℚ)^25 * 2^25 = (2 : ℚ)^50 := by rw [← pow_add]
  rw [hh]
  calc _ ≤ (2 : ℚ)^50 / 2^255 + (2 : ℚ)^50 / 2^255 := by gcongr
       _ = 1 / (2 : ℚ)^204 := by
         rw [show (255 : ℕ) = 50 + 204 + 1 from rfl, pow_add, pow_add, pow_one]
         field_simp
         <;> ring
       _ ≤ 1 / (2 : ℚ)^109 := QueryScanHistoryRealNumerics.dyadic_mono (by omega)

#print axioms join_le
#print axioms lazy_budget_mono
#print axioms lazy_budget_small
end R1Z.QueryScanRealLazyJoin
