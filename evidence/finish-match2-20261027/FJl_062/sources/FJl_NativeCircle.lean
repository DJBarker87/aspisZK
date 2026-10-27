import FIp_FirstMatch
import FJl_OpenedMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_NativeCircle
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- The installed actual comparison fixes the selected output to the circle
of the imported backend VALUES, all on the SAME native query observation. -/
theorem value {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array FIp_DotsAdapter.E 29#usize)
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (o : Port4C_QueryValues.Observation
      (Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install
        (FIp_Install.configuration err c r).query))) proof p a out g none geometry b bout) :
    CheckpointBytes5Output.ofE o.selected=FoldRuntimeAlgebra.circleWithInverses
      (CheckpointBytes5Output.ofE o.alpha0)
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 0)))
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 1)))
      (Port5Q1_OpeningValues.values o.dots) :=
  FIp_FirstMatch.selected err c r o.alpha0 o.folded o.selected o.dots o.inverse o.circle o.comparison
#print axioms value
end AspisR1.FJl_NativeCircle
end
