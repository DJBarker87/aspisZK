/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.DecoderUniqueness
noncomputable section
variable {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

def disagree (a b : I → V) : Finset I := Finset.univ.filter (fun i => a i ≠ b i)

theorem triangle_support (a b c : I → V) : disagree a c ⊆ disagree a b ∪ disagree b c := by
  intro i member
  have ne : a i ≠ c i := (Finset.mem_filter.mp member).2
  by_cases left : a i=b i
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, fun right => ne (left.trans right)⟩
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,left⟩

theorem triangle (a b c : I → V) :
    (disagree a c).card ≤ (disagree a b).card+(disagree b c).card :=
  (Finset.card_le_card (triangle_support a b c)).trans (Finset.card_union_le _ _)

theorem symmetric (a b : I → V) : disagree a b = disagree b a := by
  ext i
  simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]

/-- Generic code uniqueness. The concrete RS/circle minimum distance must
be derived from the actual encoder; it is not replaced by decoder success. -/
theorem unique_close_codeword (code : (I → V) → Prop) (distance t : Nat)
    (separation : ∀ a b, code a → code b → a≠b → distance ≤ (disagree a b).card)
    (room : 2*t < distance) (received a b : I → V) (ca : code a) (cb : code b)
    (ha : (disagree received a).card ≤ t) (hb : (disagree received b).card ≤ t) : a=b := by
  by_contra different
  have far := separation a b ca cb different
  have near := triangle a received b
  rw [symmetric a received] at near
  omega

#print axioms unique_close_codeword
end
end AspisV8Completion.DecoderUniqueness
