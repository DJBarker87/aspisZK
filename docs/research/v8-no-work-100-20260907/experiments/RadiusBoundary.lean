import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! A radius cutoff is not an extraction-failure predicate. These are
symbolic distance/uniqueness facts, not a transplanted circle-code theorem. -/
set_option autoImplicit false
namespace AspisV8.RadiusBoundary
open Finset
variable {Pos V : Type*} [DecidableEq Pos] [DecidableEq V]

def distance (D : Finset Pos) (a b : Pos → V) : ℕ :=
  (D.filter fun x => a x ≠ b x).card

theorem corruption_other_distance (D : Finset Pos) (r anchor other : Pos → V)
    (s delta : ℕ) (near : distance D r anchor ≤ s)
    (overlap : (D.filter fun x => anchor x = other x).card ≤ delta) :
    D.card ≤ s + delta + distance D r other := by
  have sub : (D.filter fun x => r x = other x) ⊆
      (D.filter fun x => r x ≠ anchor x) ∪ (D.filter fun x => anchor x = other x) := by
    intro x hx
    obtain ⟨hd,he⟩ := mem_filter.mp hx
    by_cases h : r x = anchor x
    · exact mem_union_right _ (mem_filter.mpr ⟨hd, h.symm.trans he⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hd,h⟩)
  have bound := (card_le_card sub).trans (card_union_le _ _)
  have split := card_filter_add_card_filter_not (s:=D) (fun x => r x = other x)
  change (D.filter fun x => r x ≠ anchor x).card ≤ s at near
  unfold distance
  simp only [ne_eq] at *
  omega

theorem no_anchor_inside_cutoff (C : Set (Pos → V)) (D : Finset Pos)
    (r anchor : Pos → V) (s cutoff delta : ℕ)
    (exact_distance : distance D r anchor = s)
    (code_overlap : ∀ other ∈ C, other ≠ anchor →
      (D.filter fun x => anchor x = other x).card ≤ delta)
    (cutoff_small : cutoff < s)
    (far_other : cutoff + s + delta < D.card) :
    ∀ other ∈ C, cutoff < distance D r other := by
  intro other hc
  by_cases he : other = anchor
  · simpa [he, exact_distance] using cutoff_small
  · have h := corruption_other_distance D r anchor other s delta
      (Nat.le_of_eq exact_distance) (code_overlap other hc he)
    omega

/-- Useful replacement: sparse corruption preserves a unique nearest
anchor even when an arbitrary smaller radius classifier returns none. -/
theorem unique_nearest_anchor (C : Set (Pos → V)) (D : Finset Pos)
    (r anchor : Pos → V) (s delta : ℕ)
    (near : distance D r anchor ≤ s)
    (code_overlap : ∀ other ∈ C, other ≠ anchor →
      (D.filter fun x => anchor x = other x).card ≤ delta)
    (gap : 2*s+delta < D.card) :
    ∀ other ∈ C, other ≠ anchor → distance D r anchor < distance D r other := by
  intro other hc he
  have h := corruption_other_distance D r anchor other s delta near
    (code_overlap other hc he)
  omega

theorem boundary_instance (C : Set (Pos → V)) (D : Finset Pos)
    (r anchor : Pos → V) (hD : D.card = 262144)
    (exact_distance : distance D r anchor = 9302)
    (overlap : ∀ other ∈ C, other ≠ anchor →
      (D.filter fun x => anchor x = other x).card ≤ 256) :
    (∀ other ∈ C, 9301 < distance D r other) ∧
    (∀ other ∈ C, other ≠ anchor → distance D r anchor < distance D r other) := by
  constructor
  · exact no_anchor_inside_cutoff C D r anchor 9302 9301 256 exact_distance overlap
      (by omega) (by omega)
  · exact unique_nearest_anchor C D r anchor 9302 256 (Nat.le_of_eq exact_distance)
      overlap (by omega)

/-- Actual extraction success stays outside the failure event, regardless of
where an arbitrary radius classifier sends an accepted execution. -/
theorem failure_partition (A X N T : Prop) :
    A ∧ ¬ X ↔
      (A ∧ ¬ X ∧ N) ∨
      (A ∧ ¬ X ∧ ¬ N ∧ ¬ T) ∨
      (A ∧ ¬ X ∧ ¬ N ∧ T) := by tauto

#print axioms corruption_other_distance
#print axioms no_anchor_inside_cutoff
#print axioms unique_nearest_anchor
#print axioms boundary_instance
#print axioms failure_partition
end AspisV8.RadiusBoundary
