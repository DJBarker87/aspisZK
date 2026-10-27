import R1Z.PV_Canon_Carrier
import R1Z.ProverRwSuccessScalarInverseExact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
 theorem scalar_try_inverse (ops : ExternalFuns) (x z : U32)
    (h : (ProverRwSuccessInverseInstall.selected ops).op105 x = .ok (some z)) : M z := by
  by_cases hz : x=0#u32
  · subst x
    change ProverRwSuccessInverseInstall.Src.mInv 0#u32 = .ok (some z) at h
    simp only [ProverRwSuccessInverseInstall.Src.mInv,
      ProverRwSuccessInverseSource.field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv,
      ProverRwSuccessInverseSource.field.M31.Insts.CoreCmpPartialEqM31.eq,
      ProverRwDictionaryDerived.mEq,
      ProverRwDictionaryDerivedSource.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
      ProverRwSuccessInverseSource.field.M31.ZERO,AspisR1ProducerRelease47.field.M31.ZERO,
      decide_true,bind_tc_ok,if_true] at h
    cases h
  · obtain ⟨y,hy,hc,_⟩ := ProverRwSuccessScalarInverseExact.exact_result ops x hz
    rw [hy] at h
    cases h
    exact hc
#print axioms scalar_try_inverse
end R1Z.PV_Canon
