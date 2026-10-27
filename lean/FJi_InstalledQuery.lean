import FJi_QueryJoin
import FIq_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_InstalledQuery
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
abbrev E := FIp_DotsAdapter.E

def ops {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) : Ops :=
  Port4C_RowStd.install (Port5Q1_QueryPorts.install (FIq_Install.configuration err c r).query)

theorem slot {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) : (ops err c r).op20=FIp_DotsAdapter.dots := rfl

/-- VALUE join at the actual installed composition call; all selected operands
are obtained by inversion of that call, with its original proof/p/accumulator. -/
theorem value {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array E 29#usize) (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (answer : core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
    (hg : FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g))
    (run : verifier.candidate.query_values (ops err c r) proof p a g none geometry pending=ok answer) :
    FJi_QueryJoin.Meaning (ops err c r) proof a.next g :=
  FJi_QueryJoin.value (ops err c r) proof p a g none geometry pending answer (slot err c r) hg run
#print axioms slot
#print axioms value
end AspisR1.FJi_InstalledQuery
end
