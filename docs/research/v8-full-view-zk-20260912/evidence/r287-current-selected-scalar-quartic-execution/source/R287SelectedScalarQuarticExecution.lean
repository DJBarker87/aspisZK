import AspisR286QueryFieldRaw
import AspisV8R19.R240HalfExecution
import AspisV8R19.R165QuarticExecution

/-! Selected-source quartic negation and multiplication by a base scalar.
Canonical encoding is explicit. No point/vector traversal or batch claim. -/
set_option autoImplicit false
namespace AspisV8R19.R287SelectedScalarQuarticExecution
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)
open R164ProductExecution (encode)
noncomputable section
abbrev rawNeg := AspisR286QueryFieldRaw.aspis_core.field.QM31.neg
abbrev rawMulM := AspisR286QueryFieldRaw.aspis_core.field.QM31.mul_m31

theorem neg_encode (z : QM31Exact) : rawNeg (encode z) = .ok (encode (-z)) := by
  simp only [rawNeg,AspisR286QueryFieldRaw.aspis_core.field.QM31.neg,
    R164ProductExecution.encode,R163ComplexExecution.cm_neg,bind_tc_ok,
    QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg]

theorem mul_m31_encode (z : QM31Exact) (x : M31Exact) :
    rawMulM (encode z) (encodeBase x) =
      .ok (encode (z * algebraMap CM31Exact QM31Exact (R240HalfExecution.mapBase x))) := by
  have he : (⟨z.re*R240HalfExecution.mapBase x,z.im*R240HalfExecution.mapBase x⟩ : QM31Exact) =
      z * algebraMap CM31Exact QM31Exact (R240HalfExecution.mapBase x) := by
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
  calc
    rawMulM (encode z) (encodeBase x) =
        .ok (encode (⟨z.re*R240HalfExecution.mapBase x,z.im*R240HalfExecution.mapBase x⟩ : QM31Exact)) := by
      simp only [rawMulM,AspisR286QueryFieldRaw.aspis_core.field.QM31.mul_m31,
        R164ProductExecution.encode,R240HalfExecution.cm_mul_m31_exact,bind_tc_ok]
    _ = .ok (encode (z * algebraMap CM31Exact QM31Exact (R240HalfExecution.mapBase x))) := by rw [he]

#print axioms neg_encode
#print axioms mul_m31_encode
end
end AspisV8R19.R287SelectedScalarQuarticExecution
