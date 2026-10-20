import Aeneas

/-! R22 unsigned primitive bridge. Successful checked execution implies the
same wrapping result and excludes overflow for that operation. To obtain the
needed deployed-to-model direction, a caller must separately establish total
checked execution (e.g. from its preserved canonicality/range invariants). -/
set_option autoImplicit false
namespace AspisR1.CheckedWrappingScalarAgreement
open Aeneas Aeneas.Std Result

theorem add_success_agrees {ty : UScalarTy} (x y z : UScalar ty)
    (h : UScalar.add x y = ok z) :
    UScalar.wrapping_add x y = z ∧ x.val+y.val < 2^ty.numBits := by
  have he := UScalar.add_equiv x y
  have hop : (x+y : Result (UScalar ty)) = UScalar.add x y := rfl
  simp only [hop,h] at he
  refine ⟨?_,he.1⟩
  apply UScalar.eq_of_val_eq
  change (x.bv+y.bv).toNat = z.bv.toNat
  exact congrArg BitVec.toNat he.2.2.symm

theorem sub_success_agrees {ty : UScalarTy} (x y z : UScalar ty)
    (h : UScalar.sub x y = ok z) :
    UScalar.wrapping_sub x y = z ∧ y.val ≤ x.val := by
  have he := UScalar.sub_equiv x y
  have hop : (x-y : Result (UScalar ty)) = UScalar.sub x y := rfl
  simp only [hop,h] at he
  refine ⟨?_,he.1⟩
  apply UScalar.eq_of_val_eq
  change (x.bv-y.bv).toNat = z.bv.toNat
  exact congrArg BitVec.toNat he.2.2.symm

theorem mul_success_agrees {ty : UScalarTy} (x y z : UScalar ty)
    (h : UScalar.mul x y = ok z) :
    UScalar.wrapping_mul x y = z ∧ x.val*y.val < 2^ty.numBits := by
  have he := UScalar.mul_equiv x y
  have hop : (x*y : Result (UScalar ty)) = UScalar.mul x y := rfl
  simp only [hop,h] at he
  refine ⟨?_,?_⟩
  · apply UScalar.eq_of_val_eq
    change (x.bv*y.bv).toNat = z.bv.toNat
    exact congrArg BitVec.toNat he.2.2.symm
  · have hb := he.1
    rw [UScalar.max] at hb
    have hp : 0 < 2^ty.numBits := Nat.pow_pos (by decide)
    omega

#print axioms add_success_agrees
#print axioms sub_success_agrees
#print axioms mul_success_agrees
end AspisR1.CheckedWrappingScalarAgreement
