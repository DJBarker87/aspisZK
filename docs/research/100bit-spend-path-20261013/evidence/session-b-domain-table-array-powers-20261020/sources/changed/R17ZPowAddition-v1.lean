import R17TableBasePowerBridge
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17ZPowAddition
open R17TableBasePowerBridge

instance : CommMonoid ZC where
  one := oneZ
  mul := zMul
  one_mul := by
    intro x
    change zMul oneZ x = x
    ext <;> simp [zMul, oneZ]
  mul_one := by
    intro x
    change zMul x oneZ = x
    ext <;> simp [zMul, oneZ]
  mul_assoc := by
    intro x y z
    change zMul (zMul x y) z = zMul x (zMul y z)
    ext <;> simp only [zMul] <;> ring
  mul_comm := by
    intro x y
    change zMul x y = zMul y x
    ext <;> simp only [zMul] <;> ring
  npow := fun n x => Nat.rec oneZ (fun _ y => zMul y x) n
  npow_zero := by intro x; rfl
  npow_succ := by intro x n; rfl

 theorem zPow_eq_pow (x : ZC) (n : Nat) : zPow x n = x ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp only [zPow]
      rfl
    | succ k =>
      have hhalf : (k + 1) / 2 < k + 1 := by omega
      have ihhalf := ih ((k + 1) / 2) hhalf
      have hmod_cases : (k + 1) % 2 = 0 ∨ (k + 1) % 2 = 1 := by omega
      cases hmod_cases with
      | inl heven =>
        have hbool : ((k + 1) % 2 == 0) = true := by simp [heven]
        have hform : k + 1 = 2 * ((k + 1) / 2) := by omega
        simp only [zPow, hbool, ↓reduceIte]
        rw [ihhalf]
        change x ^ ((k + 1) / 2) * x ^ ((k + 1) / 2) = x ^ (k + 1)
        rw [← pow_add]
        congr 1
        omega
      | inr hodd =>
        have hbool : ((k + 1) % 2 == 0) = false := by simp [show (k + 1) % 2 ≠ 0 by omega]
        have hform : k + 1 = 2 * ((k + 1) / 2) + 1 := by omega
        simp only [zPow, hbool, ↓reduceIte]
        rw [ihhalf]
        change (x ^ ((k + 1) / 2) * x ^ ((k + 1) / 2)) * x = x ^ (k + 1)
        calc
          (x ^ ((k + 1) / 2) * x ^ ((k + 1) / 2)) * x =
              x ^ (((k + 1) / 2) + ((k + 1) / 2)) * x := by rw [← pow_add]
          _ = x ^ (((k + 1) / 2) + ((k + 1) / 2) + 1) := by
            calc
              x ^ (((k + 1) / 2) + ((k + 1) / 2)) * x =
                  x ^ (((k + 1) / 2) + ((k + 1) / 2)) * x ^ 1 := by simp
              _ = x ^ (((k + 1) / 2) + ((k + 1) / 2) + 1) := by rw [← pow_add]
          _ = x ^ (k + 1) := by congr 1; omega

theorem zPow_add (x : ZC) (a b : Nat) :
    zPow x (a + b) = zMul (zPow x a) (zPow x b) := by
  rw [zPow_eq_pow, zPow_eq_pow, zPow_eq_pow]
  exact pow_add x a b

#print axioms zPow_eq_pow
#print axioms zPow_add

end R17ZPowAddition
