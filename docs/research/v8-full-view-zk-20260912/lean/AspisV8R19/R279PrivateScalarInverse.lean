import AspisR278PrivateInverseRaw
import AspisV8R19.R251PrivateAddSub
import AspisV8R19.R161WrappedMulExecution

/-! Encoded scalar negation and inversion through the actual private R278
wrappers. Inversion retains the explicit nonzero premise, while zero returns
the source assertion failure. -/
set_option autoImplicit false
namespace AspisV8R19.R279PrivateScalarInverse
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase (M31Exact)
open AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm (B)
open ComplexBaseExecution (encodeBase encodeBase_val)
noncomputable section

theorem b_neg_encode (x : M31Exact) :
    AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.neg
      (encodeBase x) = .ok (encodeBase (-x)) := by
  change AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B.sub
    (AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO)
    (encodeBase x) = .ok (encodeBase (-x))
  have hzero :
      AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO =
        encodeBase (0 : M31Exact) := by
    apply UScalar.eq_of_val_eq
    simp [AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO,
      encodeBase_val]
  rw [hzero]
  simpa using AspisV8R19.R251PrivateAddSub.b_sub_encode (0 : M31Exact) x

theorem b_inv_encode (x : M31Exact) (hx : x ≠ 0) :
    AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.inv
      (encodeBase x) = .ok (encodeBase x⁻¹) := by
  simp only [AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.inv,
    AspisV8R19.R161WrappedMulExecution.inv_encode x hx, bind_tc_ok]

theorem b_inv_zero :
    AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.inv
      (encodeBase (0 : M31Exact)) = .fail .assertionFailure := by
  simp only [AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.inv,
    AspisV8R19.R161WrappedMulExecution.inv_zero, bind_tc_fail]

#print axioms b_neg_encode
#print axioms b_inv_encode
#print axioms b_inv_zero
end
end AspisV8R19.R279PrivateScalarInverse
