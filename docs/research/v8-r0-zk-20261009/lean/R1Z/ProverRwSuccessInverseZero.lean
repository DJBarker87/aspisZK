import R1Z.ProverRwSuccessQuarticInverseExact
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessInverseZero
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitPrimitive47 ProverCommitSubfieldOps47

theorem m_zero : ProverRwSuccessInverseInstall.Src.mInv 0#u32=.ok none := by
  simp [ProverRwSuccessInverseInstall.Src.mInv,
    ProverRwSuccessInverseSource.field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv,
    ProverRwSuccessInverseSource.field.M31.Insts.CoreCmpPartialEqM31.eq,
    ProverRwDictionaryDerived.mEq,
    ProverRwDictionaryDerivedSource.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    ProverRwSuccessInverseSource.field.M31.ZERO,AspisR1ProducerRelease47.field.M31.ZERO]

theorem c_zero : ProverRwSuccessInverseTotal.Src.cInv
    (ProverRwSuccessComplexInverseExact.input ⟨0#u32,0#u32⟩)=.ok none := by
  unfold ProverRwSuccessInverseTotal.Src.cInv
    ProverRwSuccessInverseSource.field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
  have mul : ProverRwSuccessInverseSource.field.M31.mul 0#u32 0#u32=.ok 0#u32 := by
    have word : ProverCommitInverse48.wordMul 0#u32 0#u32=0#u32 :=
      UScalar.eq_of_val_eq (by rfl)
    simpa only [word] using ProverCommitInverse48.release_multiply 0#u32 0#u32
  have add : ProverRwSuccessInverseSource.field.M31.add 0#u32 0#u32=.ok 0#u32 := by
    simp [ProverRwSuccessInverseSource.field.M31.add,AspisR1ProducerRelease47.field.M31.add,
      AspisR1ProducerRelease47.field.P,lift]
    exact UScalar.eq_of_val_eq (by rfl)
  have inv := m_zero
  unfold ProverRwSuccessInverseInstall.Src.mInv at inv
  simp [ProverRwSuccessComplexInverseExact.input,ProverRwDictionaryTower.fromC,
    ProverCommitNativeC49.source,ProverCommitRelease47.convC,fromC,mul,add,inv,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    read_discriminant]
#print axioms m_zero
#print axioms c_zero
end R1Z.ProverRwSuccessInverseZero
