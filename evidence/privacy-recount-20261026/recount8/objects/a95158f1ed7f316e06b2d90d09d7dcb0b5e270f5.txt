import R1Z.ProverRwSuccessArithmeticTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessInverseTotal
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
open ProverRwSuccessArithmeticTotal
namespace Src
abbrev cInv := ProverRwSuccessInverseSource.field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
abbrev qInv := ProverRwSuccessInverseInstall.Src.qInv
end Src
variable [ExternalTypes]

theorem c_inv_total (ops : ExternalFuns) (x : C) : Total (Src.cInv x) := by
  unfold Src.cInv ProverRwSuccessInverseSource.field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
  apply bind_total (m_mul _ _);intro a
  apply bind_total (m_mul _ _);intro b
  apply bind_total (m_add _ _);intro norm
  apply bind_total (ProverRwSuccessInverseInstall.m_total ops _);intro inverse
  cases inverse with
  | none => exact ⟨none,by simp [
      ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      read_discriminant]⟩
  | some val =>
    simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok]
    apply bind_total (m_mul _ _);intro _
    apply bind_total (m_neg _);intro _
    apply bind_total (m_mul _ _);intro _
    exact ok_total _

theorem c_mul_total (x y : C) : Total (ProverRwSuccessInverseSource.field.CM31.mul x y) :=
  mapped_total _ _ (c_mul _ _)
theorem c_sub_total (x y : C) : Total (ProverRwSuccessInverseSource.field.CM31.sub x y) :=
  mapped_total _ _ (c_sub _ _)
theorem c_neg_total (x : C) : Total (ProverRwSuccessInverseSource.field.CM31.neg x) :=
  mapped_total _ _ (c_neg _)

theorem q_inv_total (ops : ExternalFuns) (x : Q) : Total (Src.qInv x) := by
  unfold Src.qInv ProverRwSuccessInverseInstall.Src.qInv
    ProverRwSuccessInverseSource.field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
  simp only [ProverRwSuccessInverseSource.field.CM31.new,
    ProverRwDictionaryBytes.Src.complex,
    ProverRwDictionaryBytesSource.aspis_core.field.CM31.new,bind_tc_ok]
  apply bind_total (c_mul_total _ _);intro _
  apply bind_total (c_mul_total _ _);intro _
  apply bind_total (c_mul_total _ _);intro _
  apply bind_total (c_sub_total _ _);intro norm
  apply bind_total (c_inv_total ops _);intro inverse
  cases inverse with
  | none => exact ⟨none,by simp [
      ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      read_discriminant]⟩
  | some val =>
    simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok]
    apply bind_total (c_mul_total _ _);intro _
    apply bind_total (c_neg_total _);intro _
    apply bind_total (c_mul_total _ _);intro _
    exact ok_total _

theorem q_neg_total (x : Q) : Total (ProverRwSuccessInverseInstall.Src.qNeg x) := by
  unfold ProverRwSuccessInverseInstall.Src.qNeg ProverRwSuccessInverseSource.field.QM31.neg
  apply bind_total (c_neg_total _);intro _
  apply bind_total (c_neg_total _);intro _
  exact ok_total _
#print axioms c_inv_total
#print axioms c_mul_total
#print axioms c_sub_total
#print axioms c_neg_total
#print axioms q_inv_total
#print axioms q_neg_total
end R1Z.ProverRwSuccessInverseTotal
