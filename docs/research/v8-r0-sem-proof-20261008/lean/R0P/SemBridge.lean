import R0P.SemDecision
import R0P.SemD3
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

/-! G14′ stop finding for the independent-input weighted-degree criterion.

`Poseidon.lean:31–53` gives the two linear-layer identities below, without
using any round-constant entry. `Poseidon.lean:202–207,344–352` and
`state_only_poseidon.rs:389–398,589–615` then give the source-audit route:
two quintic rounds have a degree-25 leading part, and the literal leading
residual multiplies that part by both block and low-row selector factors.

The identification of the actual leadingPair coefficient with 35^31 remains
a symbolic source-audit finding here; it is not a theorem about the actual
round constants in this module. The final theorem certifies the degree of
the stated monomial once its nonzero coefficient is supplied. No constant
table, permutation or trace is evaluated. No `VirtualDeg` theorem, actual
challenge-coordinate counterexample, or implementation bridge is claimed. -/


namespace R0P.SemBridge
open Polynomial

variable {K : Type} [Field K]

/-- The literal four-word matrix sends a constant vector to seven times it. -/
theorem poseidonMat4_constant (x : K) :
    poseidonMat4 (fun _ : Fin 4 => x) = fun _ => 7 * x := by
  funext lane
  fin_cases lane <;> simp [poseidonMat4] <;> ring

#print axioms poseidonMat4_constant

/-- Four local groups and their column sum multiply a constant vector by 35. -/
theorem poseidonExternalLinear_constant (x : K) :
    poseidonExternalLinear (fun _ : Fin 16 => x) = fun _ => 35 * x := by
  funext lane
  simp only [poseidonExternalLinear, poseidonMat4_constant]
  ring

#print axioms poseidonExternalLinear_constant

/-- The candidate weighted-degree witness, with its coefficient kept symbolic.
Both selector factors and the current-opening factor have weight one. -/
theorem weighted_witness_degree (h35 : (35 : K) ≠ 0) :
    (C (-((35 : K) ^ 31)) * (X : K[X]) ^ 27).natDegree = 27 := by
  exact Polynomial.natDegree_C_mul_X_pow 27 (-((35 : K) ^ 31))
    (neg_ne_zero.mpr (pow_ne_zero 31 h35))

#print axioms weighted_witness_degree

end R0P.SemBridge
