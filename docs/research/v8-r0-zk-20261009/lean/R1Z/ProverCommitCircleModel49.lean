import AspisFormal.V5FriNaturalBasisRadix4
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! The selected model of the source circle-weight formula, using only the
active natural-line basis. This does not establish Rust refinement. -/
namespace R1Z.ProverCommitCircleModel49

open AspisCircleTensorBinding

variable {F : Type*} [Field F]

def circleWeight (x y : F) (r : Nat) : F :=
  naturalLineValue x (r / 2) * if r % 2 = 0 then 1 else y

theorem circle_four (x y : F) (n : Nat) (k : Fin 4) :
    circleWeight x y (4 * n + k.val) =
      naturalLineValue (doubledFactor x 1) n * ![1, y, x, x * y] k := by
  have hd0 : (4 * n) / 2 = 2 * n := by omega
  have hd1 : (4 * n + 1) / 2 = 2 * n := by omega
  have hd2 : (4 * n + 2) / 2 = 2 * n + 1 := by omega
  have hd3 : (4 * n + 3) / 2 = 2 * n + 1 := by omega
  have hm0 : (4 * n) % 2 = 0 := by omega
  have hm1 : (4 * n + 1) % 2 = 1 := by omega
  have hm2 : (4 * n + 2) % 2 = 0 := by omega
  have hm3 : (4 * n + 3) % 2 = 1 := by omega
  fin_cases k <;> simp [circleWeight, hd0, hd1, hd2, hd3, hm0, hm1, hm2, hm3,
    show ¬ (1 : Nat) = 0 by decide, ↓reduceIte,
    AspisV5FriNaturalBasisRadix4.naturalLineValue_two_mul,
    AspisV5FriNaturalBasisRadix4.naturalLineValue_two_mul_add_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, mul_one] <;> ring

#print axioms circle_four

end R1Z.ProverCommitCircleModel49


/-! Symbolic base-four decomposition of the selected circle weights.
This decomposes the selected mathematical weight model into base-four factors;
it does not establish Rust refinement. -/

namespace R1Z.ProverCommitCircleModel49

open AspisCircleTensorBinding
open AspisV5FriNaturalBasisRadix4

variable {F : Type*} [Field F]

def T2 (x : F) : F := doubledFactor x 1

def T4 (x : F) : F := doubledFactor x 2

def radixFactor (x : F) (slot : Fin 4) : F :=
  ![1, x, doubledFactor x 1, x * doubledFactor x 1] slot

def firstFactor (x y : F) (slot : Fin 4) : F := ![1, y, x, x * y] slot

theorem naturalLineValue_zero (x : F) : naturalLineValue x 0 = 1 := by
  simp [AspisCircleTensorBinding.naturalLineValue]

theorem naturalLineValue_radix4_digit (x : F) (j : Nat) :
    naturalLineValue x j =
      naturalLineValue (doubledFactor x 2) (j / 4) *
        radixFactor x ⟨j % 4, Nat.mod_lt _ (by decide)⟩ := by
  have hj : j = 4 * (j / 4) + j % 4 := by omega
  calc
    naturalLineValue x j =
        naturalLineValue x (4 * (j / 4) + j % 4) := by
          exact congrArg (naturalLineValue x) hj
    _ = naturalLineValue (doubledFactor x 2) (j / 4) *
          radixFactor x ⟨j % 4, Nat.mod_lt _ (by decide)⟩ := by
      simpa [radixFactor] using
        (AspisV5FriNaturalBasisRadix4.naturalLineValue_four_mul_add x (j / 4)
          ⟨j % 4, Nat.mod_lt _ (by decide)⟩)

theorem circleWeight_base4 (x y : F) (j : Fin 1024) :
    R1Z.ProverCommitCircleModel49.circleWeight x y j.val =
      firstFactor x y ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩ *
      radixFactor (doubledFactor x 1)
        ⟨(j.val / 4) % 4, Nat.mod_lt _ (by decide)⟩ *
      radixFactor (doubledFactor (doubledFactor x 1) 2)
        ⟨(j.val / 16) % 4, Nat.mod_lt _ (by decide)⟩ *
      radixFactor (doubledFactor (doubledFactor (doubledFactor x 1) 2) 2)
        ⟨(j.val / 64) % 4, Nat.mod_lt _ (by decide)⟩ *
      radixFactor
        (doubledFactor (doubledFactor (doubledFactor (doubledFactor x 1) 2) 2) 2)
        ⟨(j.val / 256) % 4, Nat.mod_lt _ (by decide)⟩ := by
  have hcircle := R1Z.ProverCommitCircleModel49.circle_four x y (j.val / 4)
    ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩
  have hj : j.val = 4 * (j.val / 4) + j.val % 4 := by omega
  have hdiv1 : (j.val / 4) / 4 = j.val / 16 := by omega
  have hdiv2 : (j.val / 16) / 4 = j.val / 64 := by omega
  have hdiv3 : (j.val / 64) / 4 = j.val / 256 := by omega
  have hdiv4 : (j.val / 256) / 4 = j.val / 1024 := by omega
  have hzero : j.val / 1024 = 0 := by omega
  have h1 := naturalLineValue_radix4_digit (doubledFactor x 1) (j.val / 4)
  have h2 := naturalLineValue_radix4_digit
    (doubledFactor (doubledFactor x 1) 2) (j.val / 16)
  have h3 := naturalLineValue_radix4_digit
    (doubledFactor (doubledFactor (doubledFactor x 1) 2) 2) (j.val / 64)
  have h4 := naturalLineValue_radix4_digit
    (doubledFactor (doubledFactor (doubledFactor (doubledFactor x 1) 2) 2) 2)
    (j.val / 256)
  have hbase :
      R1Z.ProverCommitCircleModel49.circleWeight x y j.val =
        naturalLineValue (doubledFactor x 1) (j.val / 4) *
          firstFactor x y ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩ := by
    calc
      R1Z.ProverCommitCircleModel49.circleWeight x y j.val =
          R1Z.ProverCommitCircleModel49.circleWeight x y
            (4 * (j.val / 4) + j.val % 4) :=
        congrArg (R1Z.ProverCommitCircleModel49.circleWeight x y) hj
      _ = naturalLineValue (doubledFactor x 1) (j.val / 4) *
            firstFactor x y ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩ := by
        simpa [firstFactor] using hcircle
  rw [hbase, h1, hdiv1, h2, hdiv2, h3, hdiv3, h4, hdiv4,
    hzero, naturalLineValue_zero]
  ring

#print axioms naturalLineValue_radix4_digit
#print axioms circleWeight_base4

end R1Z.ProverCommitCircleModel49
