import NDO_JFv_TX2_CircleGeometry
import NDO_JFv_TX2_GeometryFixture
import RPz8_Rc10_Top
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_Query0Obligation
open Aeneas Aeneas.Std Result

def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value10_3.value

def Goal {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 0)
    (JFv_TX2_CircleGeometry.inverse err seed 0)=ok selected

theorem selected_read : Array.index_usize (JFn_Values.value 0) 3#usize=ok selected :=
  JFn_Values10.selected

theorem necessary {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C)
    (gate : Goal err seed) :
    FoldRuntimeAlgebra.circleWithInverses (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE (S7JoinBasisMachine.decode JFv_TX2_Row10.value.x)⁻¹)
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE (S7JoinBasisMachine.decode JFv_TX2_Row10.value.y)⁻¹)
      (Port5Q1_OpeningValues.values (JFs_TX2_Dots.value 0))=CheckpointBytes5Output.ofE selected := by
  obtain ⟨out,run,_,formula⟩ := JFv_TX2_CircleGeometry.source err seed 0
  have same : out=selected := Result.ok.inj (run.symm.trans gate)
  exact formula.symm.trans (congrArg CheckpointBytes5Output.ofE same)

#print Goal
#print axioms selected_read
#print axioms necessary
#print axioms JFv_TX2_GeometryFixture.on_saved
#print axioms JFv_TX2_GeometryFixture.inhabited
#print axioms Rc10_Top.deployed
end AspisR1.JFv_TX2_Query0Obligation
end
