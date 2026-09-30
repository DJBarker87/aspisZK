import AspisV8R19.OracleResampling

/-! A purely finite causal first-hit union bound.

The bad predicates may depend on the complete execution sample, including
adaptive transcript roots.  The theorem only combines explicit per-step mean
bounds; it supplies no source law, independence, freshness, or cryptographic
conclusion.
-/
set_option autoImplicit false
namespace AspisV8R19.CausalFirstHitUnionBound

open OracleResampling

variable {X I : Type*} [Fintype X] [Nonempty X] [Fintype I] [DecidableEq I]

noncomputable def indicator (p : Prop) : ℚ := by
  classical
  exact if p then 1 else 0

theorem indicator_nonneg (p : Prop) : 0 ≤ indicator p := by
  classical
  unfold indicator
  split <;> norm_num

theorem firstHit_indicator_le (bad : I → X → Prop)
    (x : X) :
    indicator (∃ i, bad i x) ≤ ∑ i, indicator (bad i x) := by
  classical
  by_cases h : ∃ i, bad i x
  · obtain ⟨i, hi⟩ := h
    have hex : ∃ j, bad j x := ⟨i, hi⟩
    have hi' : indicator (bad i x) ≤ ∑ j : I, indicator (bad j x) := by
      exact Finset.single_le_sum (fun j _ => indicator_nonneg (bad j x))
        (Finset.mem_univ i)
    have hone : indicator (∃ i, bad i x) = 1 := by
      simp only [indicator, if_pos hex]
    rw [hone]
    simpa only [indicator, if_pos hi] using hi'
  · simp [indicator, h]

theorem mean_sum (f : I → X → ℚ) :
    mean (fun x => ∑ i, f i x) = ∑ i, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

theorem mean_firstHit_union_le
    (bad : I → X → Prop)
    (bound : I → ℚ)
    (hbound : ∀ i, mean (fun x => indicator (bad i x)) ≤ bound i) :
    mean (fun x => indicator (∃ i, bad i x)) ≤ ∑ i, bound i := by
  classical
  have hpoint : ∀ x : X,
      indicator (∃ i, bad i x) ≤ ∑ i, indicator (bad i x) :=
    fun x => firstHit_indicator_le bad x
  have hmean :
      mean (fun x => indicator (∃ i, bad i x)) ≤
        mean (fun x => ∑ i, indicator (bad i x)) := by
    unfold mean
    apply div_le_div_of_nonneg_right
    · exact Finset.sum_le_sum (fun x _ => hpoint x)
    · positivity
  rw [mean_sum] at hmean
  exact hmean.trans (Finset.sum_le_sum (fun i _ => hbound i))

#print axioms firstHit_indicator_le
#print axioms mean_sum
#print axioms mean_firstHit_union_le
end AspisV8R19.CausalFirstHitUnionBound
