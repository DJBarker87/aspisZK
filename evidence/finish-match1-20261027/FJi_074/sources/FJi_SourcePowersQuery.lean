import FJi_SelectedPowers
import FJi_QueryJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_SourcePowersQuery
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
abbrev E := FIp_DotsAdapter.E
/-- Join the actual powers constructor and actual query call on ONE g; the
backend canonicality condition is discharged, not reintroduced as an owner row. -/
theorem value (ops : Ops) (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (answer : core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
    (installed : ops.op20=FIp_DotsAdapter.dots)
    (canonical : AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers p.gamma))
    (powers : Tx2N_Powers.powers 29#usize p.gamma=ok g)
    (run : verifier.candidate.query_values ops proof p a g obs geometry pending=ok answer) :
    FJi_QueryJoin.Meaning ops proof a.next g :=
  FJi_QueryJoin.value ops proof p a g obs geometry pending answer installed
    (FJi_SelectedPowers.value p.gamma g canonical powers).1 run
#print axioms value
end AspisR1.FJi_SourcePowersQuery
end
