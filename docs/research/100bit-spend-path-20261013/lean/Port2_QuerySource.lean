-- Verbatim inherited query-loop definitions; module imports isolated only.
import Stage2ContinuationTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2
abbrev QueryCall := Slice U8 → verifier.Prepared → verifier.Accumulator →
  Array aspis_core.field.wide_exact.WideExact 29#usize →
  Option (verifier.Phase → Result Unit) → verifier.QueryGeometry →
  verifier.BatchedWeights → Result (core.result.Result
    (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
def verifier.candidate.query_loop_loop.body
  (call : QueryCall)
  (proof : Slice Std.U8) (p : verifier.Prepared)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (obs : Option (verifier.Phase → Result Unit))
  (geometry : verifier.QueryGeometry) (end1 : Std.Usize)
  (state : core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
  verifier.Error) :
  Result (ControlFlow (core.result.Result (verifier.Accumulator ×
    verifier.BatchedWeights) verifier.Error) (core.result.Result
    (verifier.Accumulator × verifier.BatchedWeights) verifier.Error))
  := do
  match state with
  | core.result.Result.Ok p1 =>
    let (a, pending) := p1
    if a.next >= end1
    then ok (done state)
    else
      let state1 ←
        call proof p a g obs geometry pending
      ok (cont state1)
  | core.result.Result.Err _ => ok (done state)


def verifier.candidate.query_loop_loop
  (call : QueryCall)
  (state : core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
  verifier.Error) (proof : Slice Std.U8) (p : verifier.Prepared)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (obs : Option (verifier.Phase → Result Unit))
  (geometry : verifier.QueryGeometry) (end1 : Std.Usize) :
  Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
    verifier.Error)
  := do
  loop
    (fun state1 => verifier.candidate.query_loop_loop.body call proof p g obs
      geometry end1 state1)
    state


def verifier.candidate.query_loop
  (call : QueryCall)
  (proof : Slice Std.U8) (p : verifier.Prepared) (a : verifier.Accumulator)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (obs : Option (verifier.Phase → Result Unit))
  (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
  (end1 : Std.Usize) :
  Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
    verifier.Error)
  := do
  verifier.candidate.query_loop_loop call (core.result.Result.Ok (a, pending)) proof
    p g obs geometry end1

end AspisR1Stage2
