import RPu_RawPoseidonExternalRows
import AspisV8R15.ExactTowerBase

/-! Symbolic interpretation of the four raw row formulas. No generated
function execution is asserted in this arithmetic module. -/
set_option autoImplicit false
namespace AspisR1.RawPoseidonRowField
open AspisV8R15.ExactTowerBase
open AspisR1.RawPoseidonExternalRows
abbrev M := M31Exact
abbrev Q := QM31Exact

def decodeWords (w : Fin 4 → Nat) : Q :=
  ⟨⟨(w 0 : M), (w 1 : M)⟩, ⟨(w 2 : M), (w 3 : M)⟩⟩

/-- Reduction of each unsigned accumulator preserves its field value. -/
theorem decodeWords_mod (w : Fin 4 → Nat) :
    decodeWords (fun i => w i % P) = decodeWords w := by
  ext <;> simp [decodeWords, ZMod.natCast_mod]

/-- Keep linearity symbolic; do not normalize concrete tower multiplication. -/
theorem decodeWords_add (v w : Fin 4 → Nat) :
    decodeWords (fun j => v j + w j) = decodeWords v + decodeWords w := by
  ext <;> simp [decodeWords, Nat.cast_add]

theorem decodeWords_nat_mul (n : Nat) (v : Fin 4 → Nat) :
    decodeWords (fun j => n * v j) = (n : Q) * decodeWords v := by
  induction n with
  | zero => ext <;> simp [decodeWords]
  | succ n ih =>
    simp only [Nat.succ_mul, decodeWords_add, ih, Nat.cast_succ, Nat.cast_add,
      Nat.cast_one, add_mul, one_mul]

/-- The exact quadratic tower is linear coordinate by coordinate, so the
source's four raw formulas give the existing mathematical Poseidon matrix. -/
theorem raw_rows_decode_eq_poseidonMat4
    (w : Fin 4 → Fin 4 → Nat) (r : Fin 4) :
    decodeWords (fun j => rawRowNat (fun i => w i j) r) =
      R0P.poseidonMat4 (fun i => decodeWords (w i)) r := by
  rw [← rowFormula_eq_poseidonMat4]
  fin_cases r <;>
    simp [rawRowNat, rowFormula, decodeWords_add, decodeWords_nat_mul]

#print axioms decodeWords_mod
#print axioms decodeWords_add
#print axioms decodeWords_nat_mul
#print axioms raw_rows_decode_eq_poseidonMat4
end AspisR1.RawPoseidonRowField
