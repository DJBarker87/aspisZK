import R1Z.PV_ScaleUpdate
import R1Z.PV_CurrentScale
import R1Z.PV_TraceValueInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CurrentScaleInstall
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_TraceValueInstall.selected ops with op70 := PV_CurrentScale.T}

theorem source (ops : ExternalFuns) (a : Q) (b : U32) :
    (selected ops).op70 a b = PV_CurrentScale.T a b := rfl

theorem dictionary_preserved (ops : ExternalFuns) :
    selected ops = PV_TraceValueInstall.selected ops := by
  apply PV_ScaleUpdate.preserve
  exact funext (fun a => funext (fun b => PV_CurrentScale.quartic a b))
#print axioms source
#print axioms dictionary_preserved
end R1Z.PV_CurrentScaleInstall
