import AspisFormal.V5FriNaturalBasisRadix4
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! The selected model of the source circle-weight formula, using only the
active natural-line basis. This does not establish Rust refinement. -/
namespace AspisR1.SelectedCircleWeightModel

open AspisCircleTensorBinding

variable {F : Type*} [Field F] [NeZero (2 : F)]

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

end AspisR1.SelectedCircleWeightModel
