import RPt_FJo_PhaseSlots
import RPt_FIp_FirstMatch
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_ObservedCircle
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- Native circle and comparison VALUE on either actual phase dictionary. -/
theorem value {C : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (early : Bool)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array FIp_DotsAdapter.E 29#usize) (geo : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (o : Port4C_QueryValues.Observation
      (if early then Tx1Q_QueryBridge.leaves (FIp_Install.configuration err seed r).query else
        Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install
          (FIp_Install.configuration err seed r).query))) proof p a out g none geo b bout) :
    CheckpointBytes5Output.ofE o.selected=FoldRuntimeAlgebra.circleWithInverses
      (CheckpointBytes5Output.ofE o.alpha0)
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 0)))
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 1)))
      (Port5Q1_OpeningValues.values o.dots) := by
  cases early <;>
    exact FIp_FirstMatch.selected err seed r o.alpha0 o.folded o.selected o.dots o.inverse o.circle o.comparison
#print axioms value
end AspisR1.FJo_ObservedCircle
end
