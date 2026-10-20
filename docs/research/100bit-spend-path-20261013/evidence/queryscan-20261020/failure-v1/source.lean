import QueryScanExhaustion
import AspisV8R19.Q22WordScan

/-! The actual retained Q22 recurrence: failure at the 64-word horizon implies
at most 21 distinct positions. It is not enough to bound any one collision. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryScanModelFailure
open AspisV8R19.Q22WordScan
attribute [local instance] Classical.propDecidable

 theorem keep_mem (a : List Nat) (x y : Nat) :
    y ∈ keep a x ↔ y ∈ a ∨ y = x := by
  by_cases h : x ∈ a
  · simp only [keep, if_pos h]
    constructor
    · exact Or.inl
    · rintro (hy | rfl) <;> assumption
  · simp [keep, h]

 theorem scan_covers (xs : List Nat) (s : ScanState)
    (hbudget : s.draws + xs.length ≤ 64)
    (hfail : (scan s xs).1.accepted.length < 22) :
    ∀ x, x ∈ s.accepted ∨ x ∈ xs → x ∈ (scan s xs).1.accepted := by
  induction xs generalizing s with
  | nil => simpa only [scan, List.not_mem_nil, or_false] using (fun x h => h)
  | cons x xs ih =>
    by_cases hs : s.accepted.length = 22 ∨ s.draws = 64
    · have he : scan s (x :: xs) = (s, true) := by simp only [scan, if_pos hs]
      rw [he] at hfail
      rcases hs with hc | hd
      · simp only at hfail; omega
      · simp only [List.length_cons] at hbudget; omega
    · simp only [scan, if_neg hs] at hfail ⊢
      intro y hy
      apply ih ⟨keep s.accepted x, s.draws+1⟩ (by simp only [List.length_cons] at hbudget; dsimp; omega) hfail
      rcases hy with hy | hy
      · exact Or.inl ((keep_mem _ _ _).2 (Or.inl hy))
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl ((keep_mem _ _ _).2 (Or.inr rfl))
        · exact Or.inr hy

 def words {N n : Nat} (w : Fin n → Fin N) : List Nat := List.ofFn (fun i => (w i).val)
 def initial : ScanState := ⟨[], 0⟩
 def fails {N : Nat} (w : Fin 64 → Fin N) : Prop :=
    (scan initial (words w)).1.accepted.length ≠ 22

 theorem failure_smallRange {N : Nat} (w : Fin 64 → Fin N) (hf : fails w) :
    QueryScanExhaustion.smallRange w 21 := by
  classical
  let accepted := (scan initial (words w)).1.accepted
  have hcap : accepted.length ≤ 22 := scan_count_cap initial (words w) (by simp [initial])
  have hlt : accepted.length < 22 := by change accepted.length ≠ 22 at hf; omega
  have hcover := scan_covers (words w) initial (by simp [initial, words]) hlt
  let f : Set.range w → ↥accepted.toFinset := fun x =>
    ⟨x.val.val, by
      apply List.mem_toFinset.mpr
      obtain ⟨i, hi⟩ := x.property
      apply hcover
      right
      simp only [words, List.mem_ofFn]
      exact ⟨i, congrArg Fin.val hi⟩⟩
  have hinj : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Fin.ext
    exact congrArg Subtype.val he
  have hc := Fintype.card_le_of_injective f hinj
  have ht : accepted.toFinset.card ≤ accepted.length := List.toFinset_card_le
  unfold QueryScanExhaustion.smallRange
  rw [Fintype.card_coe] at hc
  omega

 def failureProbability (N : Nat) : ℚ :=
  Fintype.card {w : Fin 64 → Fin N // fails w} / (N : ℚ)^64

 theorem failureProbability_le (N : Nat) :
    failureProbability N ≤ QueryScanExhaustion.probability N 64 21 := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Fintype.card_le_of_injective
    (fun w : {w : Fin 64 → Fin N // fails w} =>
      (⟨w.val, failure_smallRange w.val w.property⟩ :
        {w : Fin 64 → Fin N // QueryScanExhaustion.smallRange w 21}))
    (by intro a b h; exact Subtype.ext (congrArg Subtype.val h))

 theorem exhaustion_bound : failureProbability (2^18) ≤ 1 / (2 : ℚ)^454 :=
    (failureProbability_le _).trans QueryScanExhaustion.exhaustion_le_two_neg_454

#print axioms keep_mem
#print axioms scan_covers
#print axioms failure_smallRange
#print axioms failureProbability_le
#print axioms exhaustion_bound
end AspisR1.QueryScanModelFailure
