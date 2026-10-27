import R1Z.ProverRwSuccessPowerTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessInverseInstall
open Aeneas Aeneas.Std Result ProverRwFull
namespace Src
abbrev mInv := ProverRwSuccessInverseSource.field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
abbrev qInv := ProverRwSuccessInverseSource.field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
abbrev qNeg := ProverRwSuccessInverseSource.field.QM31.neg
end Src
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessBorrow.selected ops with op101 := Src.qNeg,op105 := Src.mInv,op107 := Src.qInv}

theorem m_source (ops : ExternalFuns) (x : U32) : (selected ops).op105 x=Src.mInv x := rfl
theorem q_source (ops : ExternalFuns) (x : aspis_core.field.QM31) : (selected ops).op107 x=Src.qInv x := rfl
theorem neg_source (ops : ExternalFuns) (x : aspis_core.field.QM31) : (selected ops).op101 x=Src.qNeg x := rfl

theorem m_total (ops : ExternalFuns) (x : U32) : ∃ y, (selected ops).op105 x=.ok y := by
  change ∃ y, Src.mInv x=.ok y
  unfold Src.mInv ProverRwSuccessInverseSource.field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
  simp only [ProverRwSuccessInverseSource.field.M31.Insts.CoreCmpPartialEqM31.eq,
    ProverRwDictionaryDerived.mEq,
    ProverRwDictionaryDerivedSource.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    bind_tc_ok]
  split
  · exact ⟨none,rfl⟩
  · simp only [lift,bind_tc_ok,ProverRwSuccessInverseSource.field.M31.pow]
    obtain ⟨y,hy⟩ := ProverRwSuccessPowerTotal.pow_total
      (core.convert.num.FromU64U32.from
        (U32.wrapping_sub ProverRwSuccessInverseSource.field.P 2#u32)) x
      ProverRwSuccessInverseSource.field.M31.ONE
    unfold ProverRwSuccessPowerTotal.S.pow at hy
    exact ⟨some y,by rw [hy]; rfl⟩
#print axioms m_source
#print axioms q_source
#print axioms neg_source
#print axioms m_total
end R1Z.ProverRwSuccessInverseInstall
