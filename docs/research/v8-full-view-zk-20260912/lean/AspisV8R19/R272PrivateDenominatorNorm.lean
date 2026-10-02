import AspisV8R19.R253PrivateComplexNorm
import AspisV8R19.R265PrivateNormClosures

/-! The selected private denominator norm is the canonical complex norm of
its quartic norm. Nonzero source values therefore have a nonzero encoded
base denominator. This states no claim about denominator vectors or batches. -/
set_option autoImplicit false
namespace AspisV8R19.R272PrivateDenominatorNorm
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase (QM31Exact CM31Exact M31Exact)
open AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm (C)
open R250PrivateBaseExecution (encodeC)
open ComplexBaseExecution (encodeBase encodeBase_cast)
noncomputable section

theorem denominator_norm (v : QM31Exact) :
    C.norm (encodeC (NormInverse.quarticNorm v)) =
      .ok (encodeBase (NormInverse.complexNorm (NormInverse.quarticNorm v))) := by
  exact R253PrivateComplexNorm.c_norm (NormInverse.quarticNorm v)

theorem source_denominator_nonzero (v : QM31Exact) (hv : v ≠ 0) :
    encodeBase (NormInverse.complexNorm (NormInverse.quarticNorm v)) ≠ 0#u32 := by
  have hq : NormInverse.quarticNorm v ≠ 0 :=
    NormInverse.quartic_norm_nonzero v hv
  have hc : NormInverse.complexNorm (NormInverse.quarticNorm v) ≠ 0 :=
    NormInverse.complex_norm_nonzero (NormInverse.quarticNorm v) hq
  intro hzero
  have hval :
      ((encodeBase (NormInverse.complexNorm (NormInverse.quarticNorm v))).val : M31Exact) = 0 := by
    rw [hzero]
    rfl
  rw [encodeBase_cast] at hval
  exact hc hval

#print axioms denominator_norm
#print axioms source_denominator_nonzero
end
end AspisV8R19.R272PrivateDenominatorNorm
