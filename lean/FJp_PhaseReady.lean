import FJo_ObservedCircle
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_PhaseReady
open Aeneas Aeneas.Std AspisR1Stage2
/-- Normalize only the fixed phase selection before entering value transports. -/
abbrev early {C : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array FIp_DotsAdapter.E 29#usize)
    (geo : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (o : Port4C_QueryValues.Observation (Tx1Q_QueryBridge.leaves (FIp_Install.configuration err seed r).query)
      proof p a out g none geo b bout) :
    Port4C_QueryValues.Observation
      (if (true : Bool) then Tx1Q_QueryBridge.leaves (FIp_Install.configuration err seed r).query else
        Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install (FIp_Install.configuration err seed r).query)))
      proof p a out g none geo b bout := o

abbrev late {C : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array FIp_DotsAdapter.E 29#usize)
    (geo : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (o : Port4C_QueryValues.Observation
      (Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install (FIp_Install.configuration err seed r).query)))
      proof p a out g none geo b bout) :
    Port4C_QueryValues.Observation
      (if (false : Bool) then Tx1Q_QueryBridge.leaves (FIp_Install.configuration err seed r).query else
        Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install (FIp_Install.configuration err seed r).query)))
      proof p a out g none geo b bout := o
end AspisR1.FJp_PhaseReady
end
