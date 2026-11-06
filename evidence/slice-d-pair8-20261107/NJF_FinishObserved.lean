import NJF_FinishInstantiation
import NIW_AlignFinishComposedLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJF_FinishObserved
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIT_FinishComposition
open NIW_AlignFinishComposed Classical

/-- Pair's new G changes only the evaluator; the log remains the SAME collected
invocation at the SAME decoded inputs, and is not an independent packet. -/
def detailG (r : NP6_StdModel.Reservation) (loc : Locations) (owner : FIo_Install.W)
 (v : verifier.View) (p : verifier.Prepared) : PairInfo :=
 let original:=detail r loc owner v p
 {original with native := (NJF_PairInstantiation.G r (NJF_FinishInstantiation.pairInput loc owner v p),original.native.2)}

def G (r : NP6_StdModel.Reservation) (loc : Locations) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator) : Observed Unit :=
 observe (Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
  v.round0 (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim 0#usize)
  (.round 0 v.round0 (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim) fun first=>
 observe (Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
  v.round1 (NIG_FinishAlpha.alpha p 1 (by decide)) first 1#usize)
  (.round 1 v.round1 (NIG_FinishAlpha.alpha p 1 (by decide)) first) fun claim=>
 observe ((NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z) (.new p) fun owner=>
 let pair:=detailG r loc owner v p
 attach pair (observe (NIT_ErrorTransport.full pair.native.1)
  (.pair owner p.alpha.to_slice v.final_message p.kappa) fun value=>
  if value≠claim then done (.Err .Relation) else
   observe (NHQ_PacketPorts.dot v.final_message (NHQ_WeightPort.weights a.weights.deref))
    (.dot v.final_message (NHQ_WeightPort.weights a.weights.deref)) fun actual=>
   done (if a.next≠22#usize ∨ actual≠a.rhs then .Err .Query else .Ok ()))

theorem observe_congr {A B : Type} (call : Result (Reply A)) (event : Result (Reply A) → Event)
 (f g : A → Observed B) (same : ∀ value,call=ok (.Ok value) → f value=g value) :
 observe call event f=observe call event g := by
 cases call with
 | fail err => rfl
 | div => rfl
 | ok reply => cases reply with
   | Err err => rfl
   | Ok value => simp only [observe,same value rfl]

theorem detail_source (r : NP6_StdModel.Reservation) (loc : Locations) (owner : FIo_Install.W)
 (v : verifier.View) (p : verifier.Prepared)
 (domain : NIT_PairDomain.Domain (FIo_Install.toWeights owner)
  (NFW_PowersCohort.mapArray FIo_Install.toE p.alpha) v.final_message (FIo_Install.toE p.kappa)) :
 detailG r loc owner v p=detail r loc owner v p := by
 unfold detailG
 rw [NJF_PairInstantiation.source r _ domain]
 rfl

/-- Whole observation identity, including all entered abort prefixes and all
nested pair information. No endpoint or child-success premise is retained. -/
theorem source (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) : G r loc v p a=run r loc v p a := by
 unfold G run
 apply observe_congr
 intro first firstCall
 apply observe_congr
 intro claim claimCall
 apply observe_congr
 intro owner newCall
 have caller:=NIT_PairDomain.caller r proof v p a domain owner newCall
 rw [detail_source r loc owner v p caller]

/-- The complete source event list and complete returned Result, not only the
acceptance decision, follow from the full source erasure already proved by NIW. -/
theorem source_log (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 NIW_AlignFinishComposedLog.forget (G r loc v p a)=NIW_AlignFinishExecution.run r v p a := by
 rw [source r loc proof v p a domain]
 exact NIW_AlignFinishComposedLog.source r loc proof v p a domain

#print source
#print axioms observe_congr
#print axioms detail_source
#print axioms source
#print axioms source_log
end AspisR1.NJF_FinishObserved
