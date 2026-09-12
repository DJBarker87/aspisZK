/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.DigestProjection
noncomputable section
variable {D Tail : Type*} [Fintype D] [Fintype Tail] [DecidableEq D] [DecidableEq Tail]

/-- A full-width answer represented as prefix x tail has this exact number
of preimages of a prefix target set. Concrete 32-byte/26-byte representation
must be connected by a checked bijection; full answers remain visible. -/
theorem prefix_preimage_card (targets : Finset D) :
    (targets.product (Finset.univ : Finset Tail)).card =
      targets.card*Fintype.card Tail := by simp

/-- Cancelling the hidden tail factor explains why a fixed 208-bit target
costs 2^-208 even though the adversary observes all 256 bits. -/
theorem prefix_fraction (m n t : ℚ) (hn : n ≠ 0) (ht : t ≠ 0) :
    (m*t)/(n*t) = m/n := by field_simp

#print axioms prefix_preimage_card
#print axioms prefix_fraction
end
end AspisV8Completion.DigestProjection
