import NIW_AlignFinishChildren
import NIW_AlignFinishDot
import NIT_FinishSkeleton
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishExecution
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIT_FinishComposition Classical

inductive Event where
 | round (side : Fin 2) (bytes : Slice U8) (alpha claim : FE) (outcome : Result (Reply FE))
 | new (prepared : verifier.Prepared) (outcome : Result (Reply FIo_Install.W))
 | pair (owner : FIo_Install.W) (alpha : Slice FE) (message : Slice U8) (kappa : FE)
   (outcome : Result (Reply FE))
 | dot (message : Slice U8) (weights : Slice NHE_DotBody.NQ) (outcome : Result (Reply FE))

abbrev Observed (A : Type) := Result (Reply A) × List Event

/-- Source call observation retains the entered abort event. No later event
exists on Err/fail/div; successful continuations use the actual returned value. -/
def observe {A B : Type} (call : Result (Reply A)) (event : Result (Reply A) → Event)
 (next : A → Observed B) : Observed B :=
 match call with
 | fail e => (fail e,[event call])
 | div => (div,[event call])
 | ok (.Err e) => (ok (.Err e),[event call])
 | ok (.Ok value) => let tail := next value; (tail.1,event call::tail.2)

def done (reply : Reply Unit) : Observed Unit := (ok reply,[])

def run (r : NP6_StdModel.Reservation) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) : Observed Unit :=
 observe (Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
  v.round0 (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim 0#usize)
  (.round 0 v.round0 (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim) fun first=>
 observe (Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
  v.round1 (NIG_FinishAlpha.alpha p 1 (by decide)) first 1#usize)
  (.round 1 v.round1 (NIG_FinishAlpha.alpha p 1 (by decide)) first) fun claim=>
 observe ((NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z) (.new p) fun owner=>
 match core.array.Array.index (core.ops.index.IndexSlice
  (core.slice.index.SliceIndexRangeToUsizeSlice FE)) p.alpha {«end»:=2#usize} with
 | fail e => (fail e,[])
 | div => (div,[])
 | ok alpha =>
  observe (FIo_Install.pair r owner alpha v.final_message p.kappa)
   (.pair owner alpha v.final_message p.kappa) fun pair=>
  if pair≠claim then done (.Err .Relation) else
   observe (NHQ_PacketPorts.dot v.final_message (NHQ_WeightPort.weights a.weights.deref))
    (.dot v.final_message (NHQ_WeightPort.weights a.weights.deref)) fun actual=>
   done (if a.next≠22#usize ∨ actual≠a.rhs then .Err .Query else .Ok ())

theorem erase_observe {A B : Type} (call : Result (Reply A))
 (event : Result (Reply A) → Event) (next : A → Observed B) :
 (observe call event next).1=fullBind call (fun x=>(next x).1) := by
 cases call with
 | fail e => rfl
 | div => rfl
 | ok reply => cases reply <;> rfl

#print axioms erase_observe
end AspisR1.NIW_AlignFinishExecution
