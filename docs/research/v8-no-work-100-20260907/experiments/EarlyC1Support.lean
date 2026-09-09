import Mathlib.Data.Fintype.Card

/-! Symbolic own-support uniqueness and total optional recovery. No concrete field. -/
set_option autoImplicit false
namespace AspisV8.EarlyC1Projection
open Finset
noncomputable section
local instance classicalDecision (p : Prop) : Decidable p := Classical.propDecidable p

section Generic
-- Do not carry an executable DecidableEq V interface into a concrete
-- function-space instantiation. Support is purely classical mathematics.
variable {I V M L : Type*} [Fintype I]

noncomputable def agreement (encode : M → I → V) (left right : M) : Finset I := by
  classical
  exact univ.filter fun i => encode left i = encode right i

noncomputable def support (encode : M → I → V) (received : L → I → V)
    (messages : L → M) : Finset I := by
  classical
  exact univ.filter fun i => ∀ lane, received lane i = encode (messages lane) i

/-- Two tuples with large own supports coincide. The common support is formed
only for this uniqueness proof; neither tuple must recover a batch's entire
agreement support. -/
theorem large_support_unique (encode : M → I → V)
    (received : L → I → V) (left right : L → M) (threshold cap : ℕ)
    (overlap : ∀ a b, a ≠ b → (agreement encode a b).card ≤ cap)
    (margin : Fintype.card I + cap < 2 * threshold)
    (hleft : threshold ≤ (support encode received left).card)
    (hright : threshold ≤ (support encode received right).card) : left = right := by
  classical
  let A := support encode received left
  let B := support encode received right
  have unionCap : (A ∪ B).card ≤ Fintype.card I := card_le_univ _
  have split := card_union_add_card_inter A B
  have commonLarge : cap < (A ∩ B).card := by
    change threshold ≤ A.card at hleft
    change threshold ≤ B.card at hright
    omega
  funext lane
  by_contra different
  have subset : A ∩ B ⊆ agreement encode (left lane) (right lane) := by
    intro i hi
    obtain ⟨ha,hb⟩ := mem_inter.mp hi
    have la := (mem_filter.mp ha).2 lane
    have lb := (mem_filter.mp hb).2 lane
    exact mem_filter.mpr ⟨mem_univ _, la.symm.trans lb⟩
  have count := (card_le_card subset).trans (overlap _ _ different)
  omega

noncomputable def early (encode : M → I → V) (received : L → I → V)
    (threshold : ℕ) : Option (L → M) := by
  classical
  exact if h : ∃ p, threshold ≤ (support encode received p).card then
    some (Classical.choose h) else none

theorem early_none_iff (encode : M → I → V) (received : L → I → V)
    (threshold : ℕ) :
    early encode received threshold = none ↔
      ¬ ∃ p, threshold ≤ (support encode received p).card := by
  classical
  simp only [early]
  split <;> simp_all

/-- A later tuple with sufficient support identifies the already-defined
early object. It does not make a post-challenge choice into a prechallenge one. -/
theorem early_eq_of_large_support (encode : M → I → V)
    (received : L → I → V) (p : L → M) (threshold cap : ℕ)
    (overlap : ∀ a b, a ≠ b → (agreement encode a b).card ≤ cap)
    (margin : Fintype.card I + cap < 2 * threshold)
    (hp : threshold ≤ (support encode received p).card) :
    early encode received threshold = some p := by
  classical
  have existsP : ∃ t, threshold ≤ (support encode received t).card := ⟨p,hp⟩
  simp only [early, dif_pos existsP]
  congr 1
  exact large_support_unique encode received _ p threshold cap overlap margin
    (Classical.choose_spec existsP) hp

theorem some_early_has_support (encode : M → I → V) (received : L → I → V)
    (threshold : ℕ) (p : L → M) (found : early encode received threshold = some p) :
    threshold ≤ (support encode received p).card := by
  classical
  unfold early at found
  split at found
  next h =>
    have eq := Option.some.inj found
    exact eq ▸ Classical.choose_spec h
  next h => simp at found

theorem projection_preserves_support (encode : M → I → V)
    (received : L → I → V) (p : L → M) (projectM : M → M) (projectV : V → V)
    (commutes : ∀ m i, encode (projectM m) i = projectV (encode m i))
    (fixed : ∀ lane i, projectV (received lane i) = received lane i) :
    support encode received p ⊆ support encode received (fun lane => projectM (p lane)) := by
  intro i hi
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  intro lane
  rw [commutes]
  exact (fixed lane i).symm.trans (congrArg projectV ((mem_filter.mp hi).2 lane))

theorem support_restrict {L' : Type*} (encode : M → I → V)
    (received : L → I → V) (p : L → M)
    (index : L' → L) (restricted : L' → I → V)
    (fixed : ∀ lane i, received (index lane) i = restricted lane i) :
    support encode received p ⊆ support encode restricted (fun lane => p (index lane)) := by
  intro i hi
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  intro lane
  exact (fixed lane i).symm.trans ((mem_filter.mp hi).2 (index lane))

theorem function_agreement {S W : Type*} (left right : I → S → W) :
    (univ.filter fun i => left i = right i) =
      (univ.filter fun i => ∀ s, left i s = right i s) := by
  ext i
  simp only [mem_filter, mem_univ, true_and, funext_iff]

end Generic
#print axioms large_support_unique
#print axioms early_eq_of_large_support
#print axioms early_none_iff
#print axioms some_early_has_support
#print axioms projection_preserves_support
#print axioms support_restrict
#print axioms function_agreement
end
end AspisV8.EarlyC1Projection
