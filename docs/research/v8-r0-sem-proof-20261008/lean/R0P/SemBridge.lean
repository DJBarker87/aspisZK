import R0P.SemDecision
import R0P.SemBadSets

/-! G14 stop finding: the literal successor opening need not be affine in
each original challenge coordinate. `SemView.lean` ports the polynomial
binary successor from `crates/aspis-statement/src/state_only_poseidon.rs:95–103`.
The last two MSB-first coordinates already exhibit the obstruction: after
fixing coordinate 8 to zero and coordinate 9 to x, the product of their
successor coordinates is x * (1 - x).

These bounded lemmas inspect only carries 0 and 1. They do not evaluate a
trace or a finite universe. No dot/trace bridge, honestClaims degree lemma,
or `virtual_indDeg` theorem is claimed in this finding module. -/

set_option autoImplicit false

namespace R0P.SemBridge
open R0P.SemSource

variable {K : Type} [Field K]

private theorem succCarry_zero (p : Fin 10 → K) : succCarry p 0 = 1 := by
  rfl

#print axioms succCarry_zero

private theorem succCarry_one (p : Fin 10 → K) : succCarry p 1 = p 9 := by
  change (if h : 0 < 10 then p ⟨9 - 0, by omega⟩ else 0) * succCarry p 0 = p 9
  rw [succCarry_zero]
  simp

#print axioms succCarry_one

/-- The carry entering coordinate 8 is precisely the last coordinate. -/
theorem successorPoint_eight (p : Fin 10 → K) :
    successorPoint p (8 : Fin 10) =
      p 8 + p 9 - (p 8 * p 9 + p 8 * p 9) := by
  change p 8 + succCarry p 1 - (p 8 * succCarry p 1 + p 8 * succCarry p 1) = _
  rw [succCarry_one]

#print axioms successorPoint_eight

/-- The least significant coordinate toggles with the initial carry one. -/
theorem successorPoint_nine (p : Fin 10 → K) :
    successorPoint p (9 : Fin 10) = 1 - p 9 := by
  change p 9 + succCarry p 0 - (p 9 * succCarry p 0 + p 9 * succCarry p 0) = _
  rw [succCarry_zero]
  ring

#print axioms successorPoint_nine

/-- A symbolic one-coordinate restriction of the two successor coordinates. -/
theorem successorPoint_product_at_zero (p : Fin 10 → K) (x : K)
    (h8 : p 8 = 0) (h9 : p 9 = x) :
    successorPoint p (8 : Fin 10) * successorPoint p (9 : Fin 10) = x * (1 - x) := by
  rw [successorPoint_eight, successorPoint_nine, h8, h9]
  ring

#print axioms successorPoint_product_at_zero

/-- Over a field where two is nonzero, this restricted successor product
has no affine representation as a function on the field. -/
theorem successor_product_not_affine (h2 : (2 : K) ≠ 0) :
    ¬ ∃ a c : K, ∀ x : K, x * (1 - x) = a * x + c := by
  rintro ⟨a, c, h⟩
  have hc : c = 0 := by simpa using (h 0).symm
  have ha : a = 0 := by simpa [hc] using (h 1).symm
  have hneg : (-2 : K) = 0 := by
    calc
      (-2 : K) = (2 : K) * (1 - 2) := by ring
      _ = a * 2 + c := h 2
      _ = 0 := by rw [ha, hc]; ring
  exact h2 (neg_eq_zero.mp hneg)

#print axioms successor_product_not_affine

end R0P.SemBridge
