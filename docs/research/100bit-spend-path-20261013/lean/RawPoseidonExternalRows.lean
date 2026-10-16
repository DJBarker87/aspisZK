import R0P.Poseidon

/-!
Model algebra for the four raw row formulas in the isolated `external_linear_lazy_row`
helper.  These lemmas are not a refinement theorem for its generated Rust/Aeneas
body. In particular, reduction of its `u64` limbs is a separate step.
-/
set_option autoImplicit false

namespace AspisR1.RawPoseidonExternalRows

open R0P

variable {K : Type} [Field K]

def rowFormula (v : Fin 4 → K) (r : Fin 4) : K :=
  match r.val with
  | 0 => 2 * v 0 + 3 * v 1 + v 2 + v 3
  | 1 => v 0 + 2 * v 1 + 3 * v 2 + v 3
  | 2 => v 0 + v 1 + 2 * v 2 + 3 * v 3
  | _ => 3 * v 0 + v 1 + v 2 + 2 * v 3

theorem rowFormula_eq_poseidonMat4 (v : Fin 4 → K) (r : Fin 4) :
    rowFormula v r = poseidonMat4 v r := by
  fin_cases r <;> simp [rowFormula, poseidonMat4] <;> ring

/-- The raw integer formulas used before reduction. -/
def rawRowNat (v : Fin 4 → Nat) (r : Fin 4) : Nat :=
  match r.val with
  | 0 => 2 * v 0 + 3 * v 1 + v 2 + v 3
  | 1 => v 0 + 2 * v 1 + 3 * v 2 + v 3
  | 2 => v 0 + v 1 + 2 * v 2 + 3 * v 3
  | _ => 3 * v 0 + v 1 + v 2 + 2 * v 3

theorem rawRowNat_lt_two_pow_35
    (v : Fin 4 → Nat) (r : Fin 4)
    (h : ∀ i, v i < 2^32) : rawRowNat v r < 2^35 := by
  fin_cases r <;> simp [rawRowNat] <;> have h0 := h 0 <;> have h1 := h 1 <;>
    have h2 := h 2 <;> have h3 := h 3 <;> omega

theorem rawRowNat_lt_two_pow_62
    (v : Fin 4 → Nat) (r : Fin 4)
    (h : ∀ i, v i < 2^32) : rawRowNat v r < 2^62 := by
  have hsmall := rawRowNat_lt_two_pow_35 v r h
  omega

end AspisR1.RawPoseidonExternalRows

#print axioms AspisR1.RawPoseidonExternalRows.rowFormula_eq_poseidonMat4
#print axioms AspisR1.RawPoseidonExternalRows.rawRowNat_lt_two_pow_35
#print axioms AspisR1.RawPoseidonExternalRows.rawRowNat_lt_two_pow_62
