import R1Z.PV_Op223_SelectedFields
import R1Z.PV_Op223_ExtractBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Op223_P6Bridge
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem body (ops : ExternalFuns) :
    PV_Ext_IndexClosed.compress_tagged_tuple_loop.body =
      @ProverRwP6CompressSource.compress_loop.body _ (PV_CurrentScaleInstall.selected ops) := by
  funext values lambda out power i
  unfold PV_Ext_IndexClosed.compress_tagged_tuple_loop.body
    ProverRwP6CompressSource.compress_loop.body
  simp only [PV_Op223_SelectedFields.scale ops, PV_Op223_SelectedFields.add ops,
    PV_Op223_SelectedFields.mul ops, aspis_core.field.QM31.mul_m31,
    aspis_core.field.QM31.add, aspis_core.field.QM31.mul]

theorem loop (ops : ExternalFuns) :
    PV_Ext_IndexClosed.compress_tagged_tuple_loop =
      @ProverRwP6CompressSource.compress_loop _ (PV_CurrentScaleInstall.selected ops) := by
  funext values lambda out power i
  unfold PV_Ext_IndexClosed.compress_tagged_tuple_loop ProverRwP6CompressSource.compress_loop
  rw [body ops]

theorem reference (ops : ExternalFuns) :
    PV_Op223_Applied.prover_shared.compress_tagged_tuple =
      @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops) := by
  rw [PV_Op223_ExtractBridge.extraction]
  funext tag values lambda
  unfold PV_Ext_IndexClosed.compress_tagged_tuple ProverRwP6CompressSource.compress
  simp only [PV_Op223_SelectedFields.cm_from ops, PV_Op223_SelectedFields.qm_from ops,
    aspis_core.field.CM31.from_m31, aspis_core.field.QM31.from_cm31, loop ops]
#print axioms body
#print axioms loop
#print axioms reference
end R1Z.PV_Op223_P6Bridge
