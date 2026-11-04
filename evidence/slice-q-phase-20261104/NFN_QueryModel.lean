import NFN_COMBINED_IMPORT
import NFG_QueryLoopSource
set_option autoImplicit false
noncomputable section
namespace NFN_QueryModel
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open NFG_QueryLoopDefs
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

/-- Reuse NFG's arbitrary-state step and partial-Result induction at the
actual query_loop wrapper. The SAME original inputs and geometry are retained. -/
theorem root (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (pending : verifier.BatchedWeights) (finish : Usize) (fuel : Nat)
 (budget : Budget finish fuel (.Ok (a,pending))) (geometry : verifier.QueryGeometry) :
 run (fun a b => Port3_NativeQueryBody.verifier.candidate.query_values ops proof p a g none geometry b)
  finish fuel (.Ok (a,pending)) =
 Port3_NativeQueryBody.verifier.candidate.query_loop ops proof p a g none geometry pending finish :=
 NFG_QueryLoopSource.complete ops proof p g geometry finish fuel (.Ok (a,pending)) budget

/-- Every failure/divergence/error prefix is retained before query iteration. -/
def stage (makeGeometry : Result (core.result.Result verifier.QueryGeometry verifier.Error))
 (query : verifier.QueryGeometry → Result State) : Result State := do
 let answer ← makeGeometry
 match answer with
 | .Err error => ok (.Err error)
 | .Ok geometry => query geometry

/-- Compose the original geometry Result and query-loop model without choosing
an independently successful geometry, child reply or producer. -/
theorem geometry_then_query (queries : Array U32 22#usize) (start finish : Usize)
 (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (pending : verifier.BatchedWeights) (fuel : Nat)
 (budget : Budget finish fuel (.Ok (a,pending))) :
 stage (resultMap NFN_NEW_GeometryRawInterface.answer
   (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish))
  (fun geometry => run
   (fun a b => Port3_NativeQueryBody.verifier.candidate.query_values ops proof p a g none geometry b)
   finish fuel (.Ok (a,pending))) =
 stage (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range
   NFN_NEW_GeometryDictionary.adopted queries start finish)
  (fun geometry => Port3_NativeQueryBody.verifier.candidate.query_loop
   ops proof p a g none geometry pending finish) := by
 rw [NFN_NEW_GeometryComplete.complete_raw]
 have child : (fun geometry => run
   (fun a b => Port3_NativeQueryBody.verifier.candidate.query_values ops proof p a g none geometry b)
   finish fuel (.Ok (a,pending))) =
  (fun geometry => Port3_NativeQueryBody.verifier.candidate.query_loop
   ops proof p a g none geometry pending finish) :=
  funext (root ops proof p a g pending finish fuel budget)
 rw [child]

/-- Equality of the complete model Result preserves its persistent state and
semantic effects. Native physical/error I/O interpretation remains a separate boundary. -/
theorem result_state_effects {S Event : Type} (state : S)
 (queries : Array U32 22#usize) (start finish : Usize)
 (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (pending : verifier.BatchedWeights) (fuel : Nat)
 (budget : Budget finish fuel (.Ok (a,pending))) :
 NEB_PureFrame.run (Event:=Event) state
  (stage (resultMap NFN_NEW_GeometryRawInterface.answer
    (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish))
   (fun geometry => run
    (fun a b => Port3_NativeQueryBody.verifier.candidate.query_values ops proof p a g none geometry b)
    finish fuel (.Ok (a,pending)))) =
 NEB_PureFrame.run state
  (stage (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range
    NFN_NEW_GeometryDictionary.adopted queries start finish)
   (fun geometry => Port3_NativeQueryBody.verifier.candidate.query_loop
    ops proof p a g none geometry pending finish)) :=
 NEB_PureFrame.equality state _ _
  (geometry_then_query queries start finish ops proof p a g pending fuel budget)

theorem progress (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) :
 Progress (fun a b => Port3_NativeQueryBody.verifier.candidate.query_values ops proof p a g none geometry b) :=
 NFG_QueryLoopDefs.source_progress ops proof p g geometry

theorem fuel22_budget (finish : Usize) (state : State) (bounded : finish.val ≤ 22) :
 Budget finish 22 state := by
 cases state with
 | Err error => trivial
 | Ok pair =>
  rcases pair with ⟨a,b⟩
  change finish.val ≤ a.next.val + 22
  omega
#print axioms root
#print axioms geometry_then_query
#print axioms result_state_effects
#print axioms progress
#print axioms fuel22_budget
end NFN_QueryModel
end
