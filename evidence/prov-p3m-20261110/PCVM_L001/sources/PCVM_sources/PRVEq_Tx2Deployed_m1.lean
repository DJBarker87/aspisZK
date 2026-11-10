-- PCVM_ phase P3m, scope 1: the deployed VTop Ops (DrvI_Installation.stage over the NNH Tx2 stage seed) against the Bound of PRVEq_VTop_l1.
-- Statement shape: the ten callee fields of Bound are instantiated by the deployed Ops fields themselves (xdep); the constant fields are proved
-- (with_unfolding_all rfl) against the fresh compact constants; op18 (resume) is a retained hypothesis.
import Aeneas
import PRVEq_VTop_l1
import DrvI_Installation
import NHT_Constants
import NHT_Tx2CommonModel
import NJC_ClosedCalls
import NHV_ReleaseOps
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVM_Tx2Deployed
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1

def stageNNH (base : VTop_Stages.Ops) : VTop_Stages.Ops :=
  NHT_Tx2CommonModel.constants {base with op2 := NJC_ClosedCalls.inactive, op13 := NHV_ReleaseOps.mark}

def D {F CE : Type} (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops CE) (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) : VTop_Stages.Ops :=
  DrvI_Installation.stage reserved query geo (AuS1_Install.base (stageNNH base)) finish

def xdep (y : Ext) (d : VTop_Stages.Ops) : Ext :=
  { y with
    aspis_core_field_wide_exact_WideExact_from_le_bytes := @d.op2
    verifier_candidate_parse_shape := @d.op3
    verifier_candidate_batch_merkle := @d.op5
    verifier_candidate_query_loop := @d.op6
    verifier_BatchedWeights_finish := @d.op9
    verifier_BatchedWeights_new := @d.op10
    verifier_QueryGeometry_for_range := @d.op11
    verifier_mark := @d.op13
    weights_powers := @d.op17
    verifier_finish_relation := @d.op19 }

section
variable {F CE : Type} (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
  (geo : Port3_NativeGeometryBody.Ops CE) (base : VTop_Stages.Ops)
  (finish : AspisR1Stage2.Stage2Finish.FinishOps F)

-- the gate item each callee slot stands for (definitional)
theorem slot_op2 : (D reserved query geo base finish).op2 = NJC_ClosedCalls.inactive := rfl
theorem slot_op3 : (D reserved query geo base finish).op3 = Tx2I_Install.shape := rfl
theorem slot_op5 : @(D reserved query geo base finish).op5 = @Op5T_Install.stageBatch Port4B_Install.leaves := rfl
theorem slot_op6 : (D reserved query geo base finish).op6 =
    Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install query)) := rfl
theorem slot_op9 : (D reserved query geo base finish).op9 = Port3_FlushInstall.flush := rfl
theorem slot_op10 : (D reserved query geo base finish).op10 = Port3_NativePendingInstall.source reserved := rfl
theorem slot_op11 : (D reserved query geo base finish).op11 =
    Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install geo) := rfl
theorem slot_op13 : (D reserved query geo base finish).op13 = NHV_ReleaseOps.mark := rfl
theorem slot_op17 : (D reserved query geo base finish).op17 = Tx2N_Powers.powers := rfl
theorem slot_op19 : (D reserved query geo base finish).op19 = Port4D_FinishInstall.finish finish := rfl
theorem slot_op18 : (D reserved query geo base finish).op18 = Port4A_ReaderInstall.reader reserved := rfl

-- constant fields
theorem c_op0 : @(D reserved query geo base finish).op0 = @core.option.Option.ok_or := by
  with_unfolding_all rfl
theorem c_op20 : (D reserved query geo base finish).op20 = compact.OFF_OPENINGS := by
  with_unfolding_all rfl
theorem c_op21 : (D reserved query geo base finish).op21 = compact.OFF_FINAL := by
  with_unfolding_all rfl
theorem c_op22 : (D reserved query geo base finish).op22 = compact.OFF_ROUND0 := by
  with_unfolding_all rfl
theorem c_op23 : (D reserved query geo base finish).op23 = compact.OFF_INACTIVE := by
  with_unfolding_all rfl
theorem c_op16 : (D reserved query geo base finish).op16 = ok compact.SPLIT := by
  with_unfolding_all rfl
theorem c_op14 : (D reserved query geo base finish).op14 = compact.OFF_ROUND1 := by
  with_unfolding_all rfl
theorem c_op15 : (D reserved query geo base finish).op15 = compact.OFF_FOLDED_ROOT := by
  with_unfolding_all rfl
end

#print axioms c_op0
#print axioms c_op20
#print axioms c_op21
#print axioms c_op22
#print axioms c_op23
#print axioms c_op16
#print axioms c_op14
#print axioms c_op15
end PCVM_Tx2Deployed
