import R1Z.ProverRwSuccessNativeNormalize
import R1Z.ProverRwSuccessNativeInverseTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessNativeWideTransport
open Aeneas Aeneas.Std Result ProverRwFull

theorem inverse (x : aspis_core.field.wide_exact.WideExact) :
    ProverRwSuccessNativePorts.wide_inv x=ProverRwSuccessWideSource.inverse x := by
  simp only [ProverRwSuccessNativePorts.wide_inv,
    ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv,
    ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.impl.c0,
    ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.impl.c1,
    ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.U,
    ProverRwSuccessNativePorts.aspis_core.field.CM31.ZERO,
    ProverRwSuccessNativePorts.aspis_core.field.CM31.ONE,bind_tc_ok,
    ProverRwSuccessNativeInverseTransport.q_inverse,
    ProverRwSuccessNativeNormalize.construct,ProverRwSuccessWideSource.inverse]
  all_goals rfl
#print axioms inverse
end R1Z.ProverRwSuccessNativeWideTransport
