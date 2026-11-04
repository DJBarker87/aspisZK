import Port3_NativeQueryFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFG_QueryLoopDefs
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
abbrev A := verifier.Accumulator
abbrev B := verifier.BatchedWeights
abbrev State := core.result.Result (A × B) verifier.Error
abbrev Query := A → B → Result State

def step (query : Query) (finish : Usize) (state : State) : Result (ControlFlow State State) :=
 match state with
 | .Err _ => ok (done state)
 | .Ok (a,b) => if a.next >= finish then ok (done state) else do
   let next ← query a b
   ok (cont next)

def run (query : Query) (finish : Usize) : Nat → State → Result State
 | 0,state => match state with
   | .Err _ => ok state
   | .Ok (a,_) => if a.next >= finish then ok state else div
 | fuel+1,state => match state with
   | .Err _ => ok state
   | .Ok (a,b) => if a.next >= finish then ok state else do
     let next ← query a b
     run query finish fuel next

def Budget (finish : Usize) (fuel : Nat) : State → Prop
 | .Err _ => True
 | .Ok (a,_) => finish.val ≤ a.next.val + fuel

def Progress (query : Query) : Prop := ∀ a b after pending,
 query a b=ok (.Ok (after,pending)) → after.next.val=a.next.val+1

/-- Exact arbitrary-state one-step model association, including Err, failed
child evaluation, divergence, stopped and active Ok branches. -/
theorem step_source (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (finish : Usize) (state : State) :
 step (fun a b => Port3_NativeQueryBody.verifier.candidate.query_values ops proof p a g none geometry b)
  finish state = Port3_NativeQueryBody.verifier.candidate.query_loop_loop.body
  ops proof p g none geometry finish state := by
 cases state with
 | Err error => rfl
 | Ok pair => cases pair; rfl

/-- Progress is derived from the actual emitted query body; no child-success
hypothesis is smuggled into the loop invariant. -/
theorem source_progress (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) :
 Progress (fun a b => Port3_NativeQueryBody.verifier.candidate.query_values ops proof p a g none geometry b) := by
 intro a b after pending accepted
 exact (Port3_NativeQueryFrame.query_fields ops proof p a after g none geometry b pending accepted).2.2
#print axioms step_source
#print axioms source_progress
end AspisR1.NFG_QueryLoopDefs
end
