-- PCVM_ phase P3m, scope 1: the deployed VTop Ops (DrvI_Installation.stage over the NNH Tx2 stage seed) against the Bound of PRVEq_VTop_l1.
-- Statement shape: the ten callee fields of Bound are instantiated by the deployed Ops fields themselves (xdep); the constant fields are proved
-- (with_unfolding_all rfl) against the fresh compact constants; op18 (resume) is a retained hypothesis.
import Aeneas
import PRVEq_VTop_l1
import DrvI_Installation
import NHT_Constants
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVM_Tx2Deployed
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1

-- NNH_Tx2SourceConfiguration.stage with its two slot values (NJC_ClosedCalls.inactive, NHV_ReleaseOps.mark) as parameters
-- (those modules come from a different seed generation and do not import together with the DrvI chain; see PCVM_CLASSIFICATIONS.json)
-- text-identical copy of NHT_Tx2CommonModel.constants (that module does not import together with the DrvI chain here)
def constants (ops : VTop_Stages.Ops) : VTop_Stages.Ops := {ops with
 op0 := @NHT_Constants.core.option.Option.ok_or
 op14 := NHT_Constants.compact.OFF_ROUND1
 op15 := NHT_Constants.compact.OFF_FOLDED_ROOT
 op16 := ok NHT_Constants.compact.SPLIT
 op20 := NHT_Constants.compact.OFF_OPENINGS
 op21 := NHT_Constants.compact.OFF_FINAL
 op22 := NHT_Constants.compact.OFF_ROUND0
 op23 := NHT_Constants.compact.OFF_INACTIVE
 unwrap32 := core.result.Result.unwrap core.fmt.DebugTryFromSliceError }

def stageNNH (inact : Slice Std.U8 → Result (Option aspis_core.field.wide_exact.WideExact))
    (mk : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit)
    (base : VTop_Stages.Ops) : VTop_Stages.Ops :=
  constants {base with op2 := inact, op13 := mk}

def Dep {F CE : Type} (inact : Slice Std.U8 → Result (Option aspis_core.field.wide_exact.WideExact))
    (mk : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops CE) (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) : VTop_Stages.Ops :=
  DrvI_Installation.stage reserved query geo (AuS1_Install.base (stageNNH inact mk base)) finish

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
variable {F CE : Type} (inact : Slice Std.U8 → Result (Option aspis_core.field.wide_exact.WideExact))
  (mk : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
  (geo : Port3_NativeGeometryBody.Ops CE) (base : VTop_Stages.Ops)
  (finish : AspisR1Stage2.Stage2Finish.FinishOps F)

-- the gate item each callee slot stands for (definitional)
theorem slot_op2 : (Dep inact mk reserved query geo base finish).op2 = inact := rfl
theorem slot_op3 : (Dep inact mk reserved query geo base finish).op3 = Tx2I_Install.shape := rfl
theorem slot_op5 : @(Dep inact mk reserved query geo base finish).op5 = @Op5T_Install.stageBatch Port4B_Install.leaves := rfl
theorem slot_op6 : (Dep inact mk reserved query geo base finish).op6 =
    Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install query)) := rfl
theorem slot_op9 : (Dep inact mk reserved query geo base finish).op9 = Port3_FlushInstall.flush := rfl
theorem slot_op10 : (Dep inact mk reserved query geo base finish).op10 = Port3_NativePendingInstall.source reserved := rfl
theorem slot_op11 : (Dep inact mk reserved query geo base finish).op11 =
    Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install geo) := rfl
theorem slot_op13 : (Dep inact mk reserved query geo base finish).op13 = mk := rfl
theorem slot_op17 : (Dep inact mk reserved query geo base finish).op17 = Tx2N_Powers.powers := rfl
theorem slot_op19 : (Dep inact mk reserved query geo base finish).op19 = Port4D_FinishInstall.finish finish := rfl
theorem slot_op18 : (Dep inact mk reserved query geo base finish).op18 = Port4A_ReaderInstall.reader reserved := rfl

-- constant fields
theorem c_op0 : @(Dep inact mk reserved query geo base finish).op0 = @core.option.Option.ok_or := by
  with_unfolding_all rfl
theorem c_op20 : (Dep inact mk reserved query geo base finish).op20 = compact.OFF_OPENINGS := by
  with_unfolding_all rfl
theorem c_op21 : (Dep inact mk reserved query geo base finish).op21 = compact.OFF_FINAL := by
  with_unfolding_all rfl
theorem c_op22 : (Dep inact mk reserved query geo base finish).op22 = compact.OFF_ROUND0 := by
  with_unfolding_all rfl
theorem c_op23 : (Dep inact mk reserved query geo base finish).op23 = compact.OFF_INACTIVE := by
  with_unfolding_all rfl
theorem c_op16 : (Dep inact mk reserved query geo base finish).op16 = ok compact.SPLIT := by
  with_unfolding_all rfl
theorem c_op14 : (Dep inact mk reserved query geo base finish).op14 = compact.OFF_ROUND1 := by
  with_unfolding_all rfl
theorem c_op15 : (Dep inact mk reserved query geo base finish).op15 = compact.OFF_FOLDED_ROOT := by
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
