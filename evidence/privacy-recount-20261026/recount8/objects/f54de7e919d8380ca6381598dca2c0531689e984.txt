import R1Z.ProverRwSuccessNativeInverseTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessNativeNegInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessErrorInstall.selected ops with op100 := ProverRwSuccessNativePorts.wide_neg}
theorem source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op100 x=ProverRwSuccessNativePorts.wide_neg x := rfl
theorem candidate_preserved (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op100 x=(ProverRwSuccessErrorInstall.selected ops).op100 x :=
  ProverRwSuccessNativeInverseTransport.wide_neg x
#print axioms source
#print axioms candidate_preserved
end R1Z.ProverRwSuccessNativeNegInstall
