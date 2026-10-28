import R1Z.PV_CB_Merkle
import R1Z.ProverRwSuccessNativeWideInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Field
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_Merkle.selected ops with
    op100 := ProverRwSuccessNativePorts.wide_neg
    op101 := ProverRwSuccessInverseInstall.Src.qNeg
    op105 := ProverRwSuccessInverseInstall.Src.mInv
    op107 := ProverRwSuccessInverseInstall.Src.qInv
    op109 := ProverRwSuccessNativePorts.wide_inv}
theorem op100_installed (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op100 x = ProverRwSuccessNativePorts.wide_neg x := rfl
theorem op101_installed (ops : ExternalFuns) (x : aspis_core.field.QM31) :
    (selected ops).op101 x = ProverRwSuccessInverseInstall.Src.qNeg x := rfl
theorem op105_installed (ops : ExternalFuns) (x : aspis_core.field.M31) :
    (selected ops).op105 x = ProverRwSuccessInverseInstall.Src.mInv x := rfl
theorem op107_installed (ops : ExternalFuns) (x : aspis_core.field.QM31) :
    (selected ops).op107 x = ProverRwSuccessInverseInstall.Src.qInv x := rfl
theorem op109_installed (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op109 x = ProverRwSuccessNativePorts.wide_inv x := rfl
#print axioms op100_installed
#print axioms op101_installed
#print axioms op105_installed
#print axioms op107_installed
#print axioms op109_installed
end R1Z.PV_CB_Field
