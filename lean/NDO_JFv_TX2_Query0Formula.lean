import NDO_JFv_TX2_Query0Inverse
import NDO_JFv_TX2_Query0Obligation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_Query0Formula
open Aeneas Aeneas.Std Result

theorem selected_index : 132355#u32%4#u32=ok (3#u32) := rfl

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    ∃ out, FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 0)
        (JFv_TX2_CircleGeometry.inverse err seed 0)=ok out ∧ Port4C_QueryArithmetic.CanonE out ∧
      CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.circleWithInverses
        (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
        (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 243259912)
        (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1029545577)
        (Port5Q1_OpeningValues.values (JFs_TX2_Dots.value 0)) := by
  obtain ⟨out,run,canon,formula⟩ := JFv_TX2_CircleGeometry.source err seed 0
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.circleWithInverses _
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE (S7JoinBasisMachine.decode JFv_TX2_Row10.value.x)⁻¹)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE (S7JoinBasisMachine.decode JFv_TX2_Row10.value.y)⁻¹) _ at formula
  rw [JFv_TX2_Query0Inverse.x,JFv_TX2_Query0Inverse.y] at formula
  exact ⟨out,run,canon,formula⟩

#print axioms selected_index
#print axioms source
end AspisR1.JFv_TX2_Query0Formula
end
