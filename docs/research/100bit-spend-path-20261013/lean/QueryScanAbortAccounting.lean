import QueryScanExhaustion

/-! Finite coupling/union interfaces for inserting the new abort event into
soundness or privacy. These do not assert a source-to-ROM coupling. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryScanAbortAccounting
attribute [local instance] Classical.propDecidable

 def indicator (p : Prop) : ℚ := if p then 1 else 0
 def mass {Ω : Type} [Fintype Ω] (event : Ω → Prop) : ℚ :=
   (∑ ω, indicator (event ω)) / Fintype.card Ω

 theorem transfer {Ω : Type} [Fintype Ω] (source model abort : Ω → Prop)
    (h : ∀ ω, source ω → model ω ∨ abort ω) :
    mass source ≤ mass model + mass abort := by
  have hp (ω : Ω) : indicator (source ω) ≤ indicator (model ω) + indicator (abort ω) := by
    by_cases hs : source ω
    · rcases h ω hs with hm | ha
      · simp [indicator, hs, hm]; split <;> norm_num
      · simp [indicator, hs, ha]; split <;> norm_num
    · dsimp [indicator]; rw [if_neg hs]; positivity
  unfold mass
  rw [← add_div, ← Finset.sum_add_distrib]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => hp ω)) (by positivity)

 theorem coupling {Ω : Type} [Fintype Ω] (source model abort : Ω → Prop)
    (h : ∀ ω, ¬abort ω → (source ω ↔ model ω)) :
    |mass source - mass model| ≤ mass abort := by
  have hf := transfer source model abort (fun ω hs => by
    by_cases ha : abort ω
    · exact Or.inr ha
    · exact Or.inl ((h ω ha).mp hs))
  have hb := transfer model source abort (fun ω hm => by
    by_cases ha : abort ω
    · exact Or.inr ha
    · exact Or.inl ((h ω ha).mpr hm))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

 theorem union_bound {Ω : Type} [Fintype Ω] (A : Nat)
    (abort : Fin A → Ω → Prop) (δ : ℚ) (h : ∀ i, mass (abort i) ≤ δ) :
    mass (fun ω => ∃ i, abort i ω) ≤ (A : ℚ) * δ := by
  have hp (ω : Ω) : indicator (∃ i, abort i ω) ≤ ∑ i, indicator (abort i ω) := by
    by_cases he : ∃ i, abort i ω
    · obtain ⟨i, hi⟩ := he
      rw [indicator, if_pos ⟨i, hi⟩]
      have hs := Finset.single_le_sum (f := fun i : Fin A => indicator (abort i ω))
        (fun j _ => by unfold indicator; positivity) (Finset.mem_univ i)
      simpa [indicator, hi] using hs
    · rw [indicator, if_neg he]
      apply Finset.sum_nonneg
      intro i _; unfold indicator; positivity
  have hc : mass (fun ω => ∃ i, abort i ω) ≤ ∑ i, mass (abort i) := by
    unfold mass
    rw [← Finset.sum_div, Finset.sum_comm]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => hp ω)) (by positivity)
  calc _ ≤ ∑ i, mass (abort i) := hc
       _ ≤ ∑ _i : Fin A, δ := Finset.sum_le_sum (fun i _ => h i)
       _ = (A : ℚ) * δ := by simp

#print axioms transfer
#print axioms coupling
#print axioms union_bound
end AspisR1.QueryScanAbortAccounting
