import AspisV8R17.RawReducerNat
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Narrow replay of retained raw reducer/addition proofs. Declaration bodies
from V5M31RawMulReduction lines 55–232 and QM31RustFormulaSeam lines 160–193
are retained; only imports, namespace and the minimal local aliases change.
This avoids loading the deployment/sampler aggregate for a local arithmetic
delta. It is not a new assertion of extracted Rust equality. -/
set_option autoImplicit false
namespace AspisV8R17.RawReducer
abbrev M31Exact := ZMod P

/-! ## Residue preservation (task item 4) -/

/-- `2^31` is `1` in the field, because `2^31 = P + 1`. -/
theorem cast_two_pow31 : ((2 ^ 31 : Nat) : M31Exact) = 1 := by
  rw [show (2 ^ 31 : Nat) = P + 1 from by norm_num [P], Nat.cast_add, Nat.cast_one,
    ZMod.natCast_self, zero_add]

/-- One fold preserves the residue class modulo `P`: writing
`n = 2^31 * (n / 2^31) + n % 2^31` and using `2^31 = 1` in the field collapses
the high part onto the low part. -/
theorem fold31_residue (n : Nat) : ((fold31 n : Nat) : M31Exact) = (n : M31Exact) := by
  have hsplit := Nat.div_add_mod n (2 ^ 31)
  unfold fold31
  rw [Nat.cast_add]
  conv_rhs => rw [← hsplit]
  rw [Nat.cast_add, Nat.cast_mul, cast_two_pow31]
  ring

/-- The whole reducer preserves the residue class: the `as u32` cast is exact,
each fold preserves residues, and subtracting `P` in the high branch is a
no-op modulo `P`. -/
theorem rawReduceU64_residue (x : Nat) (hx : x < 2 ^ 64) :
    ((rawReduceU64 x : Nat) : M31Exact) = (x : M31Exact) := by
  unfold rawReduceU64 condSubP
  rw [second_fold_cast_exact x hx, foldBits_eq_fold31, foldBits_eq_fold31]
  have hcond : ((if P ≤ fold31 (fold31 x) then fold31 (fold31 x) - P
      else fold31 (fold31 x) : Nat) : M31Exact) = ((fold31 (fold31 x) : Nat) : M31Exact) := by
    split
    · rename_i h; rw [Nat.cast_sub h, ZMod.natCast_self, sub_zero]
    · rfl
  rw [hcond, fold31_residue, fold31_residue]

/-- Consequently, on `u64` inputs the reducer is exactly the remainder modulo
`P`: canonical output plus preserved residue pins the value uniquely. -/
theorem rawReduceU64_eq_mod (z : Nat) (hz : z < 2 ^ 64) : rawReduceU64 z = z % P := by
  have hcanon : rawReduceU64 z < P := rawReduceU64_canonical z hz
  have hres := rawReduceU64_residue z hz
  rw [ZMod.natCast_eq_natCast_iff] at hres
  have hmodeq : rawReduceU64 z % P = z % P := hres
  rw [Nat.mod_eq_of_lt hcanon] at hmodeq
  exact hmodeq

/-! ## Multiplication seam (task items 5–8) -/

/-- Two canonical M31 factors multiply without overflowing `u64`
(`(P-1)^2 < 2^64`), which is exactly the precondition of the reducer above. -/
theorem canonicalMul_lt_two_pow64 {x y : Nat}
    (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) : x * y < 2 ^ 64 := by
  unfold CanonicalRawM31 at hx hy
  have h : x * y ≤ (P - 1) * (P - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (P - 1) * (P - 1) < 2 ^ 64 := by norm_num [P]
  omega

/-- The raw product reducer output is canonical for canonical inputs. -/
theorem rawM31Mul_canonical {x y : Nat}
    (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) : CanonicalRawM31 (rawM31Mul x y) :=
  rawReduceU64_canonical _ (canonicalMul_lt_two_pow64 hx hy)

/-- The `ZMod P` image of the raw product equals the product of the input
residues. -/
theorem rawM31Mul_residue {x y : Nat}
    (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    ((rawM31Mul x y : Nat) : M31Exact) = (x : M31Exact) * (y : M31Exact) := by
  unfold rawM31Mul
  rw [rawReduceU64_residue _ (canonicalMul_lt_two_pow64 hx hy), Nat.cast_mul]


theorem rawM31Add_canonical
    {x y : Nat} (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    CanonicalRawM31 (rawM31Add x y) := by
  unfold CanonicalRawM31 at hx hy ⊢
  unfold rawM31Add
  by_cases hhigh : P ≤ x + y
  · simp [hhigh]
    omega
  · simp [hhigh]
    omega

/-- The one-subtraction graph is the ordinary remainder because the canonical
input bounds make the unreduced sum strictly smaller than `2*P`. -/
theorem rawM31Add_eq_mod
    {x y : Nat} (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    rawM31Add x y = (x + y) % P := by
  by_cases hhigh : P ≤ x + y
  · have hreduced : x + y - P < P := by
      unfold CanonicalRawM31 at hx hy
      omega
    rw [rawM31Add, if_pos hhigh, Nat.mod_eq_sub_mod hhigh,
      Nat.mod_eq_of_lt hreduced]
  · have hlow : x + y < P := Nat.lt_of_not_ge hhigh
    rw [rawM31Add, if_neg hhigh, Nat.mod_eq_of_lt hlow]

/-- The literal Rust addition graph commutes with reduction into the exact
`ZMod (2^31-1)` model.  Both comparison branches are covered explicitly. -/
theorem residue_rawM31Add
    {x y : Nat} (_hx : CanonicalRawM31 x) (_hy : CanonicalRawM31 y) :
    ((rawM31Add x y : Nat) : M31Exact) =
      (x : M31Exact) + (y : M31Exact) := by
  by_cases hhigh : P ≤ x + y
  · rw [rawM31Add, if_pos hhigh, Nat.cast_sub hhigh, Nat.cast_add,
      ZMod.natCast_self, sub_zero]
  · rw [rawM31Add, if_neg hhigh, Nat.cast_add]


#print axioms rawReduceU64_canonical
#print axioms rawReduceU64_residue
#print axioms rawM31Mul_residue
#print axioms residue_rawM31Add
end AspisV8R17.RawReducer
