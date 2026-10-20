import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! Uniform-word exhaustion bound. No enumeration of the 2^18-position space.
A word string with at most k distinct values factors through Fin k. Counting
all such factorizations overcounts, and gives N^k * k^n / N^n. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryScanExhaustion

 def smallRange {N n : Nat} (w : Fin n → Fin N) (k : Nat) : Prop :=
  Fintype.card (Set.range w) ≤ k

 theorem factorization {N n k : Nat} (hN : 0 < N)
    (w : Fin n → Fin N) (h : smallRange w k) :
    ∃ (table : Fin k → Fin N) (labels : Fin n → Fin k),
      ∀ i, table (labels i) = w i := by
  classical
  obtain ⟨e⟩ := Fintype.nonempty_of_card_le (α := Set.range w) (β := Fin k)
    (by simpa only [Fintype.card_fin] using h)
  let table : Fin k → Fin N := fun j =>
    if hj : ∃ r, e r = j then (Classical.choose hj).val else ⟨0, hN⟩
  refine ⟨table, fun i => e ⟨w i, ⟨i, rfl⟩⟩, ?_⟩
  intro i
  have hj : ∃ r, e r = e ⟨w i, ⟨i, rfl⟩⟩ := ⟨_, rfl⟩
  dsimp only [table]
  rw [dif_pos hj]
  exact congrArg Subtype.val (e.injective (Classical.choose_spec hj))

 theorem smallRange_count {N n k : Nat} (hN : 0 < N) :
    Fintype.card {w : Fin n → Fin N // smallRange w k} ≤ N ^ k * k ^ n := by
  classical
  let witness (w : {w : Fin n → Fin N // smallRange w k}) :=
    Classical.choose (factorization hN w.val w.property)
  let labels (w : {w : Fin n → Fin N // smallRange w k}) :=
    Classical.choose (Classical.choose_spec (factorization hN w.val w.property))
  have hw (w : {w : Fin n → Fin N // smallRange w k}) :
      ∀ i, witness w (labels w i) = w.val i :=
    Classical.choose_spec (Classical.choose_spec (factorization hN w.val w.property))
  have hinj : Function.Injective (fun w => (witness w, labels w)) := by
    intro a b hab
    apply Subtype.ext
    funext i
    rw [← hw a i, ← hw b i, (Prod.mk.inj hab).1, (Prod.mk.inj hab).2]
  have hc := Fintype.card_le_of_injective _ hinj
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using hc

 /-- Exact probability of at most k distinct positions under independent uniform
 words. This is a cardinality ratio, not an assumption of uniformity on success. -/
 def probability (N n k : Nat) : ℚ :=
  Fintype.card {w : Fin n → Fin N // smallRange w k} / (N : ℚ) ^ n

 theorem probability_le {N n k : Nat} (hN : 0 < N) :
    probability N n k ≤ (N : ℚ)^k * (k : ℚ)^n / (N : ℚ)^n := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast smallRange_count (n := n) (k := k) hN

 /-- Deliberately loose symbolic bound: 21 ≤ 2^5; 18*21 + 5*64 = 698;
 18*64 = 1152 = 698+454. All powers stay symbolic. -/
 theorem exhaustion_le_two_neg_454 :
    probability (2^18) 64 21 ≤ 1 / (2 : ℚ)^454 := by
  have h := probability_le (N := 2^18) (n := 64) (k := 21) (by positivity)
  have h21 : (21 : ℚ)^64 ≤ ((2 : ℚ)^5)^64 :=
    pow_le_pow_left₀ (by positivity) (by norm_num) 64
  have hnum : ((2 : ℚ)^18)^21 * (21 : ℚ)^64 ≤ (2 : ℚ)^698 := by
    calc _ ≤ ((2 : ℚ)^18)^21 * ((2 : ℚ)^5)^64 :=
          mul_le_mul_of_nonneg_left h21 (by positivity)
         _ = (2 : ℚ)^698 := by rw [← pow_mul, ← pow_mul, ← pow_add]
  have hc : ((2^18 : Nat) : ℚ) = (2 : ℚ)^18 := by push_cast; rfl
  rw [hc] at h
  calc _ ≤ (2 : ℚ)^698 / ((2 : ℚ)^18)^64 :=
          h.trans (div_le_div_of_nonneg_right hnum (by positivity))
       _ = 1 / (2 : ℚ)^454 := by
          rw [← pow_mul]
          have he : 18*64 = 698+454 := by omega
          rw [he, pow_add]
          field_simp

 theorem exhaustion_le_two_neg_100 :
    probability (2^18) 64 21 ≤ 1 / (2 : ℚ)^100 := by
  apply exhaustion_le_two_neg_454.trans
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (by omega : 100 ≤ 454)

#print axioms factorization
#print axioms smallRange_count
#print axioms probability_le
#print axioms exhaustion_le_two_neg_454
#print axioms exhaustion_le_two_neg_100
end AspisR1.QueryScanExhaustion
