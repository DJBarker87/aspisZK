import R1Z.ProverRwSuccessNativeNegInstall
import R1Z.ProverRwSuccessNativeWideTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessNativeWideInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessNativeNegInstall.selected ops with op109 := ProverRwSuccessNativePorts.wide_inv}
theorem source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op109 x=ProverRwSuccessNativePorts.wide_inv x := rfl
theorem candidate_preserved (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op109 x=(ProverRwSuccessErrorInstall.selected ops).op109 x :=
  ProverRwSuccessNativeWideTransport.inverse x

theorem dictionary_preserved (ops : ExternalFuns) :
    selected ops=ProverRwSuccessErrorInstall.selected ops := by
  unfold selected ProverRwSuccessNativeNegInstall.selected
  rw [funext ProverRwSuccessNativeInverseTransport.wide_neg,
    funext ProverRwSuccessNativeWideTransport.inverse]
  rfl
#print axioms source
#print axioms candidate_preserved
#print axioms dictionary_preserved
end R1Z.ProverRwSuccessNativeWideInstall
