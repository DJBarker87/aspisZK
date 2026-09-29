import AspisV8R17.RawReducerNat

/-! The one-fold bound needs the product range, not merely x < 2^62. -/
set_option autoImplicit false
namespace AspisV8R19.CanonicalProduct
open AspisV8R17.RawReducer

theorem product_lt (a b : Nat) (ha : a < P) (hb : b < P) : a*b < P*P :=
  Nat.mul_lt_mul_of_lt_of_lt ha hb

theorem fold_lt (n : Nat) (hn : n < P*P) : foldBits n < 2*P := by
  rw [foldBits_eq_fold31]
  have hm := Nat.mod_lt n (by decide : 0 < 2^31)
  have hd : n / 2^31 < P := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2^31)).mpr
    unfold P at *
    omega
  unfold fold31 P at *
  omega

theorem one_fold_canonical (n : Nat) (hn : n < P*P) :
    condSubP (foldBits n) < P := by
  have h := fold_lt n hn
  unfold condSubP
  split <;> omega

theorem one_fold_mod (n : Nat) (hn : n < P*P) :
    condSubP (foldBits n) = n % P := by
  have hmod : condSubP (foldBits n) % P = n % P := by
    unfold condSubP
    split
    · rename_i h
      rw [← Nat.mod_eq_sub_mod h, foldBits_eq_fold31, fold31_mod]
    · rw [foldBits_eq_fold31, fold31_mod]
  rw [Nat.mod_eq_of_lt (one_fold_canonical n hn)] at hmod
  exact hmod

theorem general_u62_negative :
    condSubP (foldBits (2^62-1)) = P ∧ (2^62-1) % P = 0 := by decide

def guardedMul (a b : Nat) : Nat :=
  if a < P ∧ b < P then condSubP (foldBits (a*b)) else rawM31Mul a b

theorem guardedMul_eq_raw (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    guardedMul a b = rawM31Mul a b := by
  have hp : a*b < 2^64 := by
    have h := Nat.mul_lt_mul_of_lt_of_lt ha hb
    exact h
  unfold guardedMul
  split
  · rename_i hc
    rw [one_fold_mod (a*b) (product_lt a b hc.1 hc.2), rawM31Mul,
      rawReduceU64_eq_mod_nat (a*b) hp]
  · rfl

theorem guardedMul_mod (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    guardedMul a b = (a*b) % P := by
  rw [guardedMul_eq_raw a b ha hb, rawM31Mul]
  apply rawReduceU64_eq_mod_nat
  have h := Nat.mul_lt_mul_of_lt_of_lt ha hb
  exact h

theorem guardedMul_canonical (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    guardedMul a b < P := by
  rw [guardedMul_mod a b ha hb]
  exact Nat.mod_lt _ (by decide)

theorem canonical_execution_bounds (a b : Nat) (ha : a < P) (hb : b < P) :
    a*b < 2^64 ∧ foldBits (a*b) < 2^32 ∧
    condSubP (foldBits (a*b)) < P := by
  have hp := product_lt a b ha hb
  have hf := fold_lt (a*b) hp
  refine ⟨?_, ?_, one_fold_canonical (a*b) hp⟩ <;> unfold P at * <;> omega

#print axioms product_lt
#print axioms fold_lt
#print axioms one_fold_canonical
#print axioms one_fold_mod
#print axioms general_u62_negative
#print axioms guardedMul_eq_raw
#print axioms guardedMul_mod
#print axioms guardedMul_canonical
#print axioms canonical_execution_bounds
end AspisV8R19.CanonicalProduct
