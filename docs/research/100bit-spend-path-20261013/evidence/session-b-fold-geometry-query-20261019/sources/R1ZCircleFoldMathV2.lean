import AspisFormal.CircleGroupOrder
import AspisFormal.V5ComponentCConcreteFoldLinearity

set_option autoImplicit false

namespace R1ZCircleFoldMathV1

open AspisCircleGroupOrder

def rustHalf : ZMod P := 1073741824
def rustQuarter : ZMod P := 536870912

theorem two_mul_rustHalf : (2 : ZMod P) * rustHalf = 1 := by
  have e : (2 : ZMod P) * rustHalf = ((P + 1 : ℕ) : ZMod P) := by
    unfold rustHalf
    rw [show P + 1 = 2 * 1073741824 by norm_num [P], Nat.cast_mul]
    norm_num
  rw [e, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]

theorem four_mul_rustQuarter : (4 : ZMod P) * rustQuarter = 1 := by
  have e : (4 : ZMod P) * rustQuarter = ((P + 1 : ℕ) : ZMod P) := by
    unfold rustQuarter
    rw [show P + 1 = 4 * 536870912 by norm_num [P], Nat.cast_mul]
    norm_num
  rw [e, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]

theorem rustHalf_eq_inv : rustHalf = (2 : ZMod P)⁻¹ :=
  eq_inv_of_mul_eq_one_right two_mul_rustHalf

theorem rustQuarter_eq : rustQuarter = rustHalf * rustHalf := by
  have h4 : rustQuarter = (4 : ZMod P)⁻¹ := eq_inv_of_mul_eq_one_right four_mul_rustQuarter
  rw [h4, rustHalf_eq_inv, ← mul_inv]
  norm_num

variable {K : Type*} [Field K] [Algebra (ZMod P) K]

def sourceCircleFold (alpha : K) (a : Fin 4 → K) (ix iy : ZMod P) : K :=
  let h0 := (a 0 + a 1 + a 2 + a 3) * algebraMap (ZMod P) K rustQuarter
  let h1 := (a 0 - a 1 - a 2 + a 3) * algebraMap (ZMod P) K (rustQuarter * iy)
  let h2 := (a 0 + a 1 - a 2 - a 3) * algebraMap (ZMod P) K (rustQuarter * ix)
  let h3 := (a 0 - a 1 + a 2 - a 3) * algebraMap (ZMod P) K (rustQuarter * ix * iy)
  h0 + alpha * (h1 + alpha * (h2 + alpha * h3))

theorem algebraMap_rustHalf : algebraMap (ZMod P) K rustHalf = (2 : K)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have h := congrArg (algebraMap (ZMod P) K) two_mul_rustHalf
  rwa [map_mul, map_one, map_ofNat] at h

theorem sourceCircleFold_eq_model (alpha : K) (a : Fin 4 → K) (ix iy : ZMod P) :
    sourceCircleFold alpha a ix iy =
      AspisV5ComponentCConcreteFoldLinearity.circleFoldValue alpha
        (algebraMap (ZMod P) K (rustHalf * ix))
        (algebraMap (ZMod P) K (rustHalf * iy)) a := by
  rw [AspisV5ComponentCConcreteFoldLinearity.circleFoldValue,
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue_eq_polynomial]
  simp only [sourceCircleFold,
    AspisV5ComponentCConcreteFoldLinearity.lineFoldPolynomialValue,
    map_mul, map_neg, rustQuarter_eq, algebraMap_rustHalf, div_eq_mul_inv]
  ring

def sourceLineFold (alpha : K) (a : Fin 4 → K) (ix iy iz : ZMod P) : K :=
  let h0 := (a 0 + a 1 + a 2 + a 3) * algebraMap (ZMod P) K rustQuarter
  let h2 := (a 0 + a 1 - a 2 - a 3) * algebraMap (ZMod P) K (rustQuarter * iz)
  let c0 := (a 0 - a 1) * algebraMap (ZMod P) K (rustHalf * ix)
  let c1 := (a 3 - a 2) * algebraMap (ZMod P) K (rustHalf * iy)
  let h1 := (c0 + c1) * algebraMap (ZMod P) K rustHalf
  let h3 := (c0 - c1) * algebraMap (ZMod P) K (rustHalf * iz)
  h0 + alpha * (h1 + alpha * (h2 + alpha * h3))

theorem sourceLineFold_eq_model (alpha : K) (a : Fin 4 → K)
    (ix iy iz : ZMod P) :
    sourceLineFold alpha a ix iy iz =
      AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
        (algebraMap (ZMod P) K (rustHalf * ix))
        (-(algebraMap (ZMod P) K (rustHalf * iy)))
        (algebraMap (ZMod P) K (rustHalf * iz)) a := by
  rw [AspisV5ComponentCConcreteFoldLinearity.lineFoldValue_eq_polynomial]
  simp only [sourceLineFold,
    AspisV5ComponentCConcreteFoldLinearity.lineFoldPolynomialValue,
    map_mul, map_neg, rustQuarter_eq, algebraMap_rustHalf, div_eq_mul_inv]
  ring

#print axioms sourceCircleFold_eq_model
#print axioms sourceLineFold_eq_model

end R1ZCircleFoldMathV1
