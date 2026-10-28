import R1Z.ProverRwSuccessNativePorts
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessNativeInverseTransport
open Aeneas Aeneas.Std Result ProverRwFull
namespace N
abbrev m := ProverRwSuccessNativePorts.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv
abbrev c := ProverRwSuccessNativePorts.aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.try_inv
abbrev q := ProverRwSuccessNativePorts.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv
end N
namespace O
abbrev m := ProverRwSuccessInverseSource.field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
abbrev c := ProverRwSuccessInverseSource.field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
abbrev q := ProverRwSuccessInverseSource.field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
end O
theorem m_inverse (x : U32) : N.m x=O.m x := by
  simp only [N.m,O.m,ProverRwSuccessNativePorts.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv,
    ProverRwSuccessNativePorts.aspis_core.field.M31.ZERO,ProverRwSuccessNativePorts.aspis_core.field.P,
    ProverRwSuccessInverseSource.field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv,
    AspisR1ProducerRelease47.field.M31.ZERO,bind_tc_ok]

theorem c_inverse (x : aspis_core.field.CM31) : N.c x=O.c x := by
  simp only [N.c,O.c,ProverRwSuccessNativePorts.aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.try_inv,
    ProverRwSuccessInverseSource.field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv,
    show ProverRwSuccessNativePorts.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv = O.m from funext m_inverse]
  rfl

theorem q_inverse (x : aspis_core.field.QM31) : N.q x=O.q x := by
  simp only [N.q,O.q,ProverRwSuccessNativePorts.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv,
    ProverRwSuccessNativePorts.aspis_core.field.M31.ONE,AspisR1ProducerRelease47.field.M31.ONE,bind_tc_ok,
    ProverRwSuccessInverseSource.field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv,
    show ProverRwSuccessNativePorts.aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.try_inv = O.c from funext c_inverse]
  rfl

theorem wide_neg (x : aspis_core.field.wide_exact.WideExact) :
    ProverRwSuccessNativePorts.wide_neg x=ProverRwSuccessWideSource.neg x := rfl
#print axioms m_inverse
#print axioms c_inverse
#print axioms q_inverse
#print axioms wide_neg
end R1Z.ProverRwSuccessNativeInverseTransport
