import NDO_JGw_Dots0
import NDO_JGw_Inverses
import NDO_JFr_TX2_CircleArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Circle0
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    ∃ out : E, FIp_CircleQuery.circle JFq_Alpha0.scalar JGw_Dots0.value
      (JGw_Inverses.inverse err seed 0)=ok out ∧
      Port4C_QueryArithmetic.CanonE out ∧
      CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.circleWithInverses
        (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
        (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE (S7JoinBasisMachine.decode (JGp_Rows.value 0).x)⁻¹)
        (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE (S7JoinBasisMachine.decode (JGp_Rows.value 0).y)⁻¹)
        (Port5Q1_OpeningValues.values JGw_Dots0.value) := by
  obtain ⟨out,run,canon⟩ := JFr_TX2_CircleArray.source JFq_Alpha0.scalar
    JGw_Dots0.value (JGw_Inverses.inverse err seed 0) JFr_TX2_CircleArray.alpha0
    (fun j => JGw_Dots0.output_canonical _ (List.getElem_mem (by rw [JGw_Dots0.value.property];exact j.isLt)))
  have exactness := (FIp_CircleQuery.exact_circle _ _ _ _ run).1
  rw [JGw_Inverses.decoded err seed 0 0,JGw_Inverses.decoded err seed 0 1] at exactness
  exact ⟨out,run,canon,exactness⟩
#print axioms source
end AspisR1.JGw_Circle0
end
