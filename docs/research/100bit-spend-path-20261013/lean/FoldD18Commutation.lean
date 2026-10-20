import R1D18Transport
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.NormNum

/-! Nat interpretation of transport.rs:14–18. Machine-word execution and
loop extraction remain separate obligations. -/
set_option autoImplicit false
namespace AspisR1.FoldD18Commutation

def sourceRow (j : Nat) : Nat :=
  (((j >>> 0) &&& 3) <<< 6) ||| (((j >>> 2) &&& 3) <<< 8) |||
    (((j >>> 4) &&& 3) <<< 4) ||| (((j >>> 6) &&& 3) <<< 0) |||
    (((j >>> 8) &&& 3) <<< 2)

/-- Disjoint two-bit digits combine by addition, with no enumeration. -/
theorem pack_digits (a b c d e : Nat)
    (ha : a < 4) (hc : c < 4) (hd : d < 4) (he : e < 4) :
    64 * a ||| 256 * b ||| 16 * c ||| d ||| 4 * e =
      64 * a + 256 * b + 16 * c + d + 4 * e := by
  have hlow : d < 2 ^ 2 := by omega
  have hmid : 4 * e + d < 2 ^ 4 := by omega
  have hhigh : 16 * c + (4 * e + d) < 2 ^ 6 := by omega
  have htop : 64 * a + (16 * c + (4 * e + d)) < 2 ^ 8 := by omega
  calc
    _ = 256 * b ||| (64 * a ||| (16 * c ||| (4 * e ||| d))) := by ac_rfl
    _ = 256 * b + (64 * a + (16 * c + (4 * e + d))) := by
      rw [← Nat.two_pow_add_eq_or_of_lt hlow e,
        ← Nat.two_pow_add_eq_or_of_lt hmid c,
        ← Nat.two_pow_add_eq_or_of_lt hhigh a,
        ← Nat.two_pow_add_eq_or_of_lt htop b]
    _ = _ := by omega

theorem sourceRow_eq_rowNat (j : Nat) : sourceRow j = AspisR1.rowNat j := by
  have mask (x : Nat) : x &&& 3 = x % 4 :=
    Nat.and_two_pow_sub_one_eq_mod x 2
  simp only [sourceRow, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, mask]
  norm_num only [Nat.reducePow, Nat.div_one, Nat.mul_one]
  rw [show (j % 4) * 64 = 64 * (j % 4) by omega,
    show (j / 4 % 4) * 256 = 256 * (j / 4 % 4) by omega,
    show (j / 16 % 4) * 16 = 16 * (j / 16 % 4) by omega,
    show (j / 256 % 4) * 4 = 4 * (j / 256 % 4) by omega]
  exact pack_digits _ _ _ _ _ (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide))

theorem sourceRow_inverse (j : Nat) (hj : j < 1024) :
    sourceRow (sourceRow j) = j := by
  simp only [sourceRow_eq_rowNat]
  exact AspisR1.rowNat_involutive j hj

/-- A source row table, when indexed by the proved permutation, gives back
exactly the coefficient vector. This is the table correspondence premise
used by weights.rs:174–176. -/
theorem coefficients_rows {A : Type*} (m : Fin 1024 → A) (j : Fin 1024) :
    (fun r => m (AspisR1.row r)) (AspisR1.row j) = m j := by
  change m (AspisR1.row (AspisR1.row j)) = m j
  rw [AspisR1.row_involutive]

#print axioms pack_digits
#print axioms sourceRow_eq_rowNat
#print axioms sourceRow_inverse
#print axioms coefficients_rows
end AspisR1.FoldD18Commutation
