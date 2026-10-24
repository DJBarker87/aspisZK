import R1SelectedCircleWeightModel
import AspisFormal.V5FriNaturalBasisRadix4

/-! Symbolic base-four decomposition of the selected circle weights.
This decomposes the selected mathematical weight model into base-four factors;
it does not establish Rust refinement. -/

namespace AspisR1.SelectedCircleWeights

open AspisCircleTensorBinding
open AspisV5FriNaturalBasisRadix4

variable {F : Type*} [Field F] [NeZero (2 : F)]

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
    AspisR1.SelectedCircleWeightModel.circleWeight x y j.val =
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
  have hcircle := AspisR1.SelectedCircleWeightModel.circle_four x y (j.val / 4)
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
      AspisR1.SelectedCircleWeightModel.circleWeight x y j.val =
        naturalLineValue (doubledFactor x 1) (j.val / 4) *
          firstFactor x y ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩ := by
    calc
      AspisR1.SelectedCircleWeightModel.circleWeight x y j.val =
          AspisR1.SelectedCircleWeightModel.circleWeight x y
            (4 * (j.val / 4) + j.val % 4) :=
        congrArg (AspisR1.SelectedCircleWeightModel.circleWeight x y) hj
      _ = naturalLineValue (doubledFactor x 1) (j.val / 4) *
            firstFactor x y ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩ := by
        simpa [firstFactor] using hcircle
  rw [hbase, h1, hdiv1, h2, hdiv2, h3, hdiv3, h4, hdiv4,
    hzero, naturalLineValue_zero]
  ring

#print axioms naturalLineValue_radix4_digit
#print axioms circleWeight_base4

end AspisR1.SelectedCircleWeights
