import NFP_QueryTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_RejectionTrace
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts NFP_TraceTypes
open Port3_NativeQueryBody

theorem guard (continuation : M Out) :
 (if true then (pure (.Err verifier.Error.Query) : M Out) else continuation).result=
  ok (.Err verifier.Error.Query) ∧
 (if true then (pure (.Err verifier.Error.Query) : M Out) else continuation).cuts=[] := by
 constructor <;> rfl

/-- The rejected prefix retains earlier calls and has no suffix event.
Both hypotheses concern the exact cuts of this same run and its same inputs. -/
theorem prefix (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (u : Usize) (q : Slice U8) (dots : Dots)
 (inverse : Inverse) (folded : E) (values : Dots)
 (head : (NFP_TraceHead.run ops proof p a g).result=ok (u,q,dots))
 (front : (NFP_TraceFront.run ops p a geometry u q dots).result=ok (inverse,folded,values,true)) :
 (NFP_QueryTrace.run ops proof p a g geometry pending).result=ok (.Err verifier.Error.Query) ∧
 (NFP_QueryTrace.run ops proof p a g geometry pending).cuts=
  (NFP_TraceHead.run ops proof p a g).cuts++(NFP_TraceFront.run ops p a geometry u q dots).cuts := by
 simp only [NFP_QueryTrace.run,NFI_TraceResult.bindM,head,front,NFI_TraceResult.pureM,
  List.append_nil,if_true]
 exact ⟨rfl,rfl⟩
#print axioms guard
#print axioms prefix
end AspisR1.NFP_RejectionTrace
end
