import NJF_PairInstantiation
import NIW_AlignComposedRoot
import NIW_AlignFinishComposedSource
import NIW_AlignReachedBind
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJF_FinishInstantiation
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIT_FinishComposition
open NIW_AlignFinishComposed Classical

def pairInput (loc : Locations) (owner : FIo_Install.W) (v : verifier.View) (p : verifier.Prepared) :=
 NIW_AlignPairInstalled.input ⟨loc.owner,owner⟩ ⟨loc.alpha,p.alpha⟩ ⟨loc.message,v.final_message⟩
  p.kappa loc.ap0 loc.ap1 loc.common loc.low loc.scratch loc.parts

/-- FinishLog's forward oracle evaluator: same rounds, NEW ownership, full pair
Result, rejection guard, dot and final query guard. No endpoint is a parameter. -/
def G (r : NP6_StdModel.Reservation) (loc : Locations) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator) : Result (Reply Unit) :=
 fullBind (Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
  v.round0 (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim 0#usize) fun first=>
 fullBind (Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
  v.round1 (NIG_FinishAlpha.alpha p 1 (by decide)) first 1#usize) fun claim=>
 fullBind ((NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z) fun owner=>
 fullBind (NIT_ErrorTransport.full (NJF_PairInstantiation.G r (pairInput loc owner v p))) fun value=>
 if value≠claim then ok (.Err .Relation) else
 fullBind (NHQ_PacketPorts.dot v.final_message (NHQ_WeightPort.weights a.weights.deref)) fun actual=>
 ok (if a.next≠22#usize ∨ actual≠a.rhs then .Err .Query else .Ok ())

/-- Each entered pair uses the SAME NEW value and caller-proved domain. This
instantiates the corrected pair G in the existing source invocation. -/
theorem source (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) : G r loc v p a=(run r loc v p a).1 := by
 unfold G run
 rw [erase_observe]
 apply NIW_AlignReachedBind.congr
 intro first firstCall
 rw [erase_observe]
 apply NIW_AlignReachedBind.congr
 intro claim claimCall
 rw [erase_observe]
 apply NIW_AlignReachedBind.congr
 intro owner newCall
 have caller := NIT_PairDomain.caller r proof v p a domain owner newCall
 have pair := NJF_PairInstantiation.source r (pairInput loc owner v p) caller
 dsimp only [attach]
 rw [erase_observe]
 change fullBind (NIT_ErrorTransport.full (NJF_PairInstantiation.G r (pairInput loc owner v p))) _=
  fullBind (NIT_ErrorTransport.full (NIW_AlignPairPhase.run r (pairInput loc owner v p)).1) _
 rw [pair]
 apply NIW_AlignReachedBind.congr
 intro value pairCall
 split_ifs
 · rfl
 · rw [erase_observe]
   apply NIW_AlignReachedBind.congr
   intro actual dotCall
   rfl

/-- Full printed finish root; retained SAME-call Domain only. The reviewed
PairPort cut is needed only by the richer NIW source capsule, not result erasure. -/
theorem root (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=G r loc v p a :=
 (NIW_AlignFinishComposedSource.source r loc proof v p a domain).trans (source r loc proof v p a domain).symm

#print root
#print axioms source
#print axioms root
end AspisR1.NJF_FinishInstantiation
