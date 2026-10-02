import AspisR239CoeffExecutionRaw
import AspisV8R19.R236HalfWordOps
import AspisV8R19.R225LineNormAlgebra

/-! Actual selected half and CM31-by-M31 leaf execution.
The generated signed nonnegative count literals are adapted to the cached
unsigned wrapping API with count_one/count_thirty in the raw dependency.
Coefficient arrays, private R110 arithmetic and full inverse remain separate. -/
set_option autoImplicit false
namespace AspisV8R19.R240HalfExecution
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)
noncomputable section
abbrev rawBaseHalf := AspisR239CoeffExecutionRaw.aspis_core.field.M31.half
abbrev rawCMHalf := AspisR239CoeffExecutionRaw.aspis_core.field.CM31.half
abbrev rawCMMulM := AspisR239CoeffExecutionRaw.aspis_core.field.CM31.mul_m31

def mapBase (x : M31Exact) : CM31Exact := ⟨x,0⟩

theorem base_half_word (w : U32) :
    rawBaseHalf w = .ok (R228HalfEncoding.halfScalar w) := by
  simp only [rawBaseHalf,AspisR239CoeffExecutionRaw.aspis_core.field.M31.half,
    lift,bind_tc_ok]
  change Result.ok (UScalar.or (U32.wrapping_shr w 1#u32)
    (U32.wrapping_shl (UScalar.and w 1#u32) 30#u32)) = _
  exact congrArg Result.ok (R236HalfWordOps.unsigned_ops w)

theorem base_half_exact (x : M31Exact) :
    rawBaseHalf (encodeBase x) = .ok (encodeBase (x/2)) := by
  rw [base_half_word,R228HalfEncoding.halfScalar_encode]

theorem cm_half_exact (z : CM31Exact) :
    rawCMHalf (R163ComplexExecution.encode z) =
      .ok (R163ComplexExecution.encode (z/2)) := by
  have he : (⟨z.re/2,z.im/2⟩ : CM31Exact) = z/2 := by
    apply (eq_div_iff R225LineNormAlgebra.two_nonzero).2
    have hre : (2 : CM31Exact).re = (2 : M31Exact) := rfl
    have him : (2 : CM31Exact).im = 0 := rfl
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,hre,him,
        R228HalfEncoding.base_two_nonzero]
  calc
    rawCMHalf (R163ComplexExecution.encode z) =
        .ok (R163ComplexExecution.encode (⟨z.re/2,z.im/2⟩ : CM31Exact)) := by
      simp only [rawCMHalf,AspisR239CoeffExecutionRaw.aspis_core.field.CM31.half,
        R163ComplexExecution.encode,base_half_exact,bind_tc_ok]
    _ = .ok (R163ComplexExecution.encode (z/2)) := by rw [he]

theorem cm_mul_m31_exact (z : CM31Exact) (x : M31Exact) :
    rawCMMulM (R163ComplexExecution.encode z) (encodeBase x) =
      .ok (R163ComplexExecution.encode (z*mapBase x)) := by
  have he : (⟨z.re*x,z.im*x⟩ : CM31Exact) = z*mapBase x := by
    apply QuadraticAlgebra.ext <;>
      simp [mapBase,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
  calc
    rawCMMulM (R163ComplexExecution.encode z) (encodeBase x) =
        .ok (R163ComplexExecution.encode (⟨z.re*x,z.im*x⟩ : CM31Exact)) := by
      simp only [rawCMMulM,AspisR239CoeffExecutionRaw.aspis_core.field.CM31.mul_m31,
        R163ComplexExecution.encode,R161WrappedMulExecution.mul_encode,bind_tc_ok]
    _ = .ok (R163ComplexExecution.encode (z*mapBase x)) := by rw [he]

#print axioms base_half_word
#print axioms base_half_exact
#print axioms cm_half_exact
#print axioms cm_mul_m31_exact
end
end AspisV8R19.R240HalfExecution
