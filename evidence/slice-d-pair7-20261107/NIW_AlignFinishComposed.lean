import NIW_AlignPairInstalled
import NIW_AlignFinishExecution
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishComposed
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIT_FinishComposition Classical
abbrev Event := NIW_AlignFinishExecution.Event

structure Locations where
 owner : Nat
 alpha : Nat
 message : Nat
 ap0 : Nat
 ap1 : Nat
 common : Nat
 low : Nat
 scratch : Nat
 parts : Nat

structure PairInfo where
 owner : Ref FIo_Install.W
 alpha : Ref (Array FE 2#usize)
 message : Ref (Slice U8)
 kappa : FE
 locations : Locations
 native : Result NIT_PairControl.NR × NIW_AlignPairPhase.Log

def detail (r : NP6_StdModel.Reservation) (loc : Locations) (owner : FIo_Install.W)
 (v : verifier.View) (p : verifier.Prepared) : PairInfo :=
 let w : Ref FIo_Install.W := ⟨loc.owner,owner⟩
 let alpha : Ref (Array FE 2#usize) := ⟨loc.alpha,p.alpha⟩
 let message : Ref (Slice U8) := ⟨loc.message,v.final_message⟩
 ⟨w,alpha,message,p.kappa,loc,NIW_AlignPairInstalled.observed r w alpha message p.kappa
  loc.ap0 loc.ap1 loc.common loc.low loc.scratch loc.parts⟩

abbrev Observed (A : Type) := Result (Reply A) × List Event × Option PairInfo

def observe {A B : Type} (call : Result (Reply A)) (event : Result (Reply A) → Event)
 (next : A → Observed B) : Observed B :=
 match call with
 | fail err => (fail err,[event call],none)
 | div => (div,[event call],none)
 | ok (.Err err) => (ok (.Err err),[event call],none)
 | ok (.Ok value) => let tail := next value; (tail.1,event call::tail.2.1,tail.2.2)

def done (reply : Reply Unit) : Observed Unit := (ok reply,[],none)
def attach (pair : PairInfo) (tail : Observed Unit) : Observed Unit := (tail.1,tail.2.1,some pair)

def run (r : NP6_StdModel.Reservation) (loc : Locations) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator) : Observed Unit :=
 observe (Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
  v.round0 (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim 0#usize)
  (.round 0 v.round0 (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim) fun first=>
 observe (Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
  v.round1 (NIG_FinishAlpha.alpha p 1 (by decide)) first 1#usize)
  (.round 1 v.round1 (NIG_FinishAlpha.alpha p 1 (by decide)) first) fun claim=>
 observe ((NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z) (.new p) fun owner=>
 let pair := detail r loc owner v p
 attach pair (observe (NIT_ErrorTransport.full pair.native.1)
  (.pair owner p.alpha.to_slice v.final_message p.kappa) fun value=>
  if value≠claim then done (.Err .Relation) else
   observe (NHQ_PacketPorts.dot v.final_message (NHQ_WeightPort.weights a.weights.deref))
    (.dot v.final_message (NHQ_WeightPort.weights a.weights.deref)) fun actual=>
   done (if a.next≠22#usize ∨ actual≠a.rhs then .Err .Query else .Ok ()))

theorem erase_observe {A B : Type} (call : Result (Reply A))
 (event : Result (Reply A) → Event) (next : A → Observed B) :
 (observe call event next).1=fullBind call (fun value=>(next value).1) := by
 cases call with
 | fail err => rfl
 | div => rfl
 | ok reply => cases reply <;> rfl

#print axioms erase_observe
end AspisR1.NIW_AlignFinishComposed
