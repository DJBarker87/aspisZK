import R1Z.PV_DictionaryUpdate
import R1Z.PV_CurrentQuarticBridge
import R1Z.PV_ProverRwP7CoefficientsInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CurrentDictionary
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_ProverRwP7CoefficientsInstall.selected ops with
    op67 := PV_CurrentQuarticBridge.S.add, op69 := PV_CurrentQuarticBridge.S.mul}

theorem add_source (ops : ExternalFuns) (a b : Q) :
    (selected ops).op67 a b = PV_CurrentQuarticBridge.S.add a b := rfl

theorem mul_source (ops : ExternalFuns) (a b : Q) :
    (selected ops).op69 a b = PV_CurrentQuarticBridge.S.mul a b := rfl

theorem dictionary_preserved (ops : ExternalFuns) :
    selected ops = PV_ProverRwP7CoefficientsInstall.selected ops := by
  apply PV_DictionaryUpdate.preserve
  · exact (funext (fun a => funext (PV_CurrentQuarticBridge.add a)))
  · exact (funext (fun a => funext (PV_CurrentQuarticBridge.mul a)))
#print axioms add_source
#print axioms mul_source
#print axioms dictionary_preserved
end R1Z.PV_CurrentDictionary
