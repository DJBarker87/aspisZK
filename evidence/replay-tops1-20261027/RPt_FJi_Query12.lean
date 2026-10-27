import RPt_FJi_QueryJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_Query12
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
abbrev E := FIp_DotsAdapter.E
/-- SAME-query installed fast_dots VALUES at source query index 12. -/
theorem value (ops : Ops) (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (answer : core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
    (installed : ops.op20=FIp_DotsAdapter.dots)
    (hg : FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g))
    (run : verifier.candidate.query_values ops proof p {a with next:=12#usize}
      g obs geometry pending=ok answer) :
    FJi_QueryJoin.Meaning ops proof 12#usize g :=
  FJi_QueryJoin.value ops proof p {a with next:=12#usize} g obs geometry pending answer installed hg run
#print axioms value
end AspisR1.FJi_Query12
end
