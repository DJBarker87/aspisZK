import R1Z.PV_CurrentScaleInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressSelectors
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

theorem scale (ops : ExternalFuns) :
    (PV_CurrentScaleInstall.selected ops).op70 = PV_CurrentScale.T := by
  funext a b
  exact PV_CurrentScaleInstall.source ops a b

theorem add (ops : ExternalFuns) :
    (PV_CurrentScaleInstall.selected ops).op67 = PV_CurrentQuarticBridge.S.add := by
  change (PV_CurrentDictionary.selected ops).op67 = _
  funext a b
  exact PV_CurrentDictionary.add_source ops a b

theorem mul (ops : ExternalFuns) :
    (PV_CurrentScaleInstall.selected ops).op69 = PV_CurrentQuarticBridge.S.mul := by
  change (PV_CurrentDictionary.selected ops).op69 = _
  funext a b
  exact PV_CurrentDictionary.mul_source ops a b
#print axioms scale
#print axioms add
#print axioms mul
end R1Z.PV_RW_CompressSelectors
