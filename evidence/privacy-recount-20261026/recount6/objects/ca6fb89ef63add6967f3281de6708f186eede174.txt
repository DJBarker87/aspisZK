import R1Z.PV_Op223_FieldBridge_QM31_mul_m31
import R1Z.PV_CurrentScaleInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Op223_SelectedFields
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
variable [ExternalTypes]
theorem cm_from (ops : ExternalFuns) :
    PV_Ext_IndexClosed.aspis_core.field.CM31.from_m31 =
      (PV_CurrentScaleInstall.selected ops).op61 := by
  change _ = (fun a => mapResult fromC (AspisR1ProducerRelease47.field.CM31.from_m31 a))
  rw [PV_Ext_FieldBridge.CM31_from_m31]
  funext a
  simp only [AspisR1ProducerRelease47.field.CM31.from_m31,
    AspisR1ProducerRelease47.field.M31.ZERO, mapResult, fromC]

theorem qm_from (ops : ExternalFuns) :
    PV_Ext_IndexClosed.aspis_core.field.QM31.from_cm31 =
      (PV_CurrentScaleInstall.selected ops).op66 := by
  change _ = (fun c => mapResult fromQ (AspisR1ProducerRelease47.field.QM31.from_cm31 (toC c)))
  rw [PV_Op223_FieldBridge.QM31_from_cm31]
  funext c
  simp only [AspisR1ProducerRelease47.field.QM31.from_cm31,
    AspisR1ProducerRelease47.field.CM31.ZERO, mapResult, fromQ, fromC, toC]

theorem add (ops : ExternalFuns) :
    PV_Ext_IndexClosed.aspis_core.field.QM31.add =
      (PV_CurrentScaleInstall.selected ops).op67 := by
  change _ = ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add
  exact PV_Op223_FieldBridge.QM31_add

theorem mul (ops : ExternalFuns) :
    PV_Ext_IndexClosed.aspis_core.field.QM31.mul =
      (PV_CurrentScaleInstall.selected ops).op69 := by
  funext a b
  calc
    PV_Ext_IndexClosed.aspis_core.field.QM31.mul a b =
        ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul a b :=
      congrFun (congrFun PV_Op223_FieldBridge.QM31_mul a) b
    _ = (PV_CurrentScaleInstall.selected ops).op69 a b :=
      (PV_CurrentDictionary.mul_source ops a b).symm

theorem scale (ops : ExternalFuns) :
    PV_Ext_IndexClosed.aspis_core.field.QM31.mul_m31 =
      (PV_CurrentScaleInstall.selected ops).op70 := by
  change _ = ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31
  exact PV_Op223_FieldBridge.QM31_mul_m31
#print axioms cm_from
#print axioms qm_from
#print axioms add
#print axioms mul
#print axioms scale
end R1Z.PV_Op223_SelectedFields
