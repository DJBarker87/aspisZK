import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
-- Same bounded Mathlib import set as R0Z/StatisticalDistance (unified base).

/-! D15's good-alpha predicate (placed here by D17′) and the D17.2 item 8
density count. No protocol module is imported. The bad set is covered by 21
coordinate-pinning sets, each in bijection with `Fin 9 → K` through
`Fin.insertNthEquiv` (the current name of `Equiv.piFinSuccAbove`); no field
element is enumerated. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.Shift
attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K]

/-- D15: every alpha coordinate off {0,1}, and alpha 9 ≠ 1/2. -/
def GoodAlpha (a : Fin 10 → K) : Prop := (∀ j, a j ≠ 0 ∧ a j ≠ 1) ∧ a 9 ≠ 1/2

/-- The alpha rows with coordinate `j` pinned at `c`. -/
def pinned [Fintype K] [DecidableEq K] (j : Fin 10) (c : K) : Finset (Fin 10 → K) :=
  Finset.univ.filter (fun a => a j = c)

/-- Removing the pinned coordinate is a bijection onto the remaining nine. -/
def pinnedEquiv (j : Fin 10) (c : K) : {a : Fin 10 → K // a j = c} ≃ (Fin 9 → K) where
  toFun a := Fin.removeNth (α := fun _ => K) j a.1
  invFun b := ⟨Fin.insertNth (α := fun _ => K) j c b,
    Fin.insertNth_apply_same (α := fun _ => K) j c b⟩
  left_inv a := by
    obtain ⟨a, ha⟩ := a
    apply Subtype.ext
    change Fin.insertNth (α := fun _ => K) j c (Fin.removeNth (α := fun _ => K) j a) = a
    subst ha
    exact Fin.insertNth_self_removeNth (α := fun _ => K) j a
  right_inv b := by
    change Fin.removeNth (α := fun _ => K) j (Fin.insertNth (α := fun _ => K) j c b) = b
    exact Fin.removeNth_insertNth (α := fun _ => K) j c b

theorem card_pinned [Fintype K] [DecidableEq K] (j : Fin 10) (c : K) :
    (pinned j c).card = Fintype.card K ^ 9 := by
  unfold pinned
  rw [← Fintype.card_subtype, Fintype.card_congr (pinnedEquiv j c), Fintype.card_fun,
    Fintype.card_fin]

/-- A bad row has a coordinate in {0,1} or alpha 9 = 1/2. -/
theorem not_goodAlpha_subset [Fintype K] [DecidableEq K] :
    (Finset.univ : Finset (Fin 10 → K)).filter (fun a => ¬ GoodAlpha a) ⊆
      ((Finset.univ : Finset (Fin 10)).biUnion fun j => pinned j (0 : K)) ∪
      ((Finset.univ : Finset (Fin 10)).biUnion fun j => pinned j (1 : K)) ∪
      pinned 9 (1/2 : K) := by
  intro a ha
  rw [Finset.mem_filter] at ha
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  by_cases h9 : a 9 = 1/2
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h9⟩)
  · left
    by_contra hcon
    apply ha.2
    refine ⟨fun j => ⟨?_, ?_⟩, h9⟩
    · intro h0
      exact hcon (Or.inl ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩)
    · intro h1
      exact hcon (Or.inr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩)

theorem card_biUnion_pinned [Fintype K] [DecidableEq K] (c : K) :
    ((Finset.univ : Finset (Fin 10)).biUnion fun j => pinned j c).card ≤
      10 * Fintype.card K ^ 9 := by
  refine (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin 10)))
    (t := fun j => pinned j c)).trans (le_of_eq ?_)
  simp only [card_pinned, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- D17.2 item 8: at most 21 coordinate-pinning sets of size `|K|^9`. -/
theorem badAlpha_card [Fintype K] [DecidableEq K] :
    ((Finset.univ : Finset (Fin 10 → K)).filter (fun a => ¬ GoodAlpha a)).card ≤
      21 * Fintype.card K ^ 9 := by
  refine (Finset.card_le_card not_goodAlpha_subset).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (Finset.card_union_le
    ((Finset.univ : Finset (Fin 10)).biUnion fun j => pinned j (0 : K))
    ((Finset.univ : Finset (Fin 10)).biUnion fun j => pinned j (1 : K))) _).trans ?_
  have h0 := card_biUnion_pinned (K := K) 0
  have h1 := card_biUnion_pinned (K := K) 1
  have h2 := card_pinned (K := K) 9 (1/2)
  generalize Fintype.card K ^ 9 = N at h0 h1 h2 ⊢
  omega

/-- D17.2 item 8: the bad fraction of alpha rows is at most `21 / |K|`. -/
theorem badAlpha_density [Fintype K] [DecidableEq K] :
    (((Finset.univ : Finset (Fin 10 → K)).filter (fun a => ¬ GoodAlpha a)).card : ℚ) /
      (Fintype.card K : ℚ) ^ 10 ≤ 21 / Fintype.card K := by
  have hK : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hK0 : (Fintype.card K : ℚ) ≠ 0 := hK.ne'
  have hc : (((Finset.univ : Finset (Fin 10 → K)).filter (fun a => ¬ GoodAlpha a)).card : ℚ) ≤
      21 * (Fintype.card K : ℚ) ^ 9 := by
    exact_mod_cast badAlpha_card (K := K)
  calc (((Finset.univ : Finset (Fin 10 → K)).filter (fun a => ¬ GoodAlpha a)).card : ℚ) /
        (Fintype.card K : ℚ) ^ 10
      ≤ (21 * (Fintype.card K : ℚ) ^ 9) / (Fintype.card K : ℚ) ^ 10 :=
        div_le_div_of_nonneg_right hc (by positivity)
    _ = 21 / Fintype.card K := by
        rw [div_eq_div_iff (pow_ne_zero 10 hK0) hK0]
        ring

#print axioms GoodAlpha
#print axioms card_pinned
#print axioms badAlpha_card
#print axioms badAlpha_density
end R0Z.Shift
