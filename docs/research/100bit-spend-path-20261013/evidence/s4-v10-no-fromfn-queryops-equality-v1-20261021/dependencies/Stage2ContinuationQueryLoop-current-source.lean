import Stage2ContinuationTypes
import Stage2ContinuationOwnedLoop
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
namespace AspisR1Stage2
private theorem actual_body (call : QueryCall) (proof : Slice U8)
    (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry) :
    verifier.candidate.query_loop_loop.body call proof p g obs geometry 22#usize =
      Stage2ContinuationOwnedLoop.body (fun a : verifier.Accumulator => a.next.val)
        (fun a b => call proof p a g obs geometry b) := by
  funext state
  cases state with
  | Err e => rfl
  | Ok pair =>
    rcases pair with ⟨a,b⟩
    rfl

theorem emitted_twelve_ordered_calls (call : QueryCall) (proof : Slice U8)
    (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (advance : ∀ a a1 b b1, call proof p a g obs geometry b = ok (.Ok (a1,b1)) →
      a1.next.val = a.next.val + 1)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (start : a.next.val = 10)
    (h : verifier.candidate.query_loop call proof p a g obs geometry b 22#usize =
      ok (.Ok (out,bout))) :
    Stage2ContinuationLoop.Chain (fun a : verifier.Accumulator => a.next.val)
      (Stage2ContinuationOwnedLoop.adapt (fun a b => call proof p a g obs geometry b))
      a b out bout 12 := by
  apply Stage2ContinuationOwnedLoop.twelve_ordered_calls _ _ advance a out b bout start
  simpa only [verifier.candidate.query_loop, verifier.candidate.query_loop_loop,
    actual_body, Stage2ContinuationOwnedLoop.run] using h
#print axioms actual_body
#print axioms emitted_twelve_ordered_calls
end AspisR1Stage2
