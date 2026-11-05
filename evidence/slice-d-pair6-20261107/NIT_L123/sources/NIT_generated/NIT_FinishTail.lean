import NIT_PairControl
import NIT_ResultChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_FinishTail
open Aeneas Aeneas.Std Result NIT_Cuts NIT_FinishComposition AspisR1Stage2 Classical

def ops (r : NP6_StdModel.Reservation) :=
 NIG_Slots.installed r

theorem trace (r : NP6_StdModel.Reservation) (tag : U16) (i : Usize) (value : FE) :
 (ops r).op0 tag i value=ok () := rfl

theorem mark (r : NP6_StdModel.Reservation) (phase : verifier.Phase) :
 (ops r).op1 none phase=ok () := rfl

theorem ne (r : NP6_StdModel.Reservation) (x y : FE) :
 (ops r).ne x y=ok (decide (x≠y)) := rfl

def dotReply (a : verifier.Accumulator) (reply : Reply FE) : Reply Unit :=
 rbind reply fun actual=>if a.next≠22#usize ∨ actual≠a.rhs then .Err .Query else .Ok ()

/-- Actual installed comparison/trace/observer semantics at the dot return.
All eight Err arms are preserved, with no assumption of a successful dot. -/
theorem dot (r : NP6_StdModel.Reservation) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (reply : Reply FE) :
 NHQ_FinishRelationModel.afterDotReply (ops r) v p a none reply=ok (dotReply a reply) := by
 cases reply with
 | Err e=>rfl
 | Ok actual=>
  unfold NHQ_FinishRelationModel.afterDotReply dotReply rbind
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,trace,ne,mark]
  by_cases next : a.next=22#usize <;> by_cases value : actual=a.rhs <;> simp [next,value]

def afterPair (r : NP6_StdModel.Reservation) (v : verifier.View) (a : verifier.Accumulator)
 (weights : Slice NHE_DotBody.NQ) (claim : FE) (reply : Reply FE) : Result (Reply Unit) :=
 fullBind (ok reply) fun pair=>if pair≠claim then ok (.Err .Relation) else
  fullBind (NHQ_PacketPorts.dot v.final_message weights) fun actual=>
   ok (dotReply a (.Ok actual))

theorem pair (r : NP6_StdModel.Reservation) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (weights : Slice NHE_DotBody.NQ) (claim : FE) (reply : Reply FE) :
 NHT_FinishRelationModel.afterPairPacket (ops r) v p a none weights claim reply=
 afterPair r v a weights claim reply := by
 cases reply with
 | Err e=>rfl
 | Ok value=>
  unfold NHT_FinishRelationModel.afterPairPacket afterPair fullBind
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,trace,ne,mark]
  by_cases different : value≠claim
  · simp [different]
  · simp only [different,decide_false,ite_false]
    apply NIT_PairControl.bind_ext
    intro result
    cases result with
    | Err e=>rfl
    | Ok actual=>exact dot r v p a (.Ok actual)

#print axioms trace
#print axioms mark
#print axioms ne
#print axioms dot
#print axioms pair
end AspisR1.NIT_FinishTail
