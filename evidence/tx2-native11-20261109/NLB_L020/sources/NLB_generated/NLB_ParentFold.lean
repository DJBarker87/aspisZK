import NLB_ObservedSteps
import NLB_Transition
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Auxiliary semantic fold against NJJ_Common.run, retaining the complete
native-input/frame family at C07 and all rejected/abort prefixes. The two
Result projections are NOT the exact child row packets and earn no row credit.
In particular the Merkle projection is not licensed by (bb)/(bc) transport. -/
theorem semantic_fold (wr rr fr : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 (nativeResume : Resume) (nativeMerkle modelMerkle : Merkle)
 (resumeProjection : ResumeProjection wr nativeResume)
 (merkleProjection : MerkleProjection nativeMerkle modelMerkle)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (headlineSize : proof.val.length=57607)
 (observe : NKE_QueryInput.Args → QueryObservation)
 (cuts : QueryCuts wr rr fr modelMerkle d pub proof ck hash observe)
 (before : List Event) :
 let w:=queryWindow (window rr fr loc nativeResume nativeMerkle d hash) observe
 let p:=NKE_CommonProgram.run wr rr modelMerkle (finish fr) d pub proof ck hash none
 G w p before=.done (NJJ_Common.run wr rr modelMerkle (finish fr) d pub proof ck hash none)
  (before++(run wr rr modelMerkle (finish fr) d pub proof ck hash none).events) := by
 dsimp only
 have localSteps : ∀ e∈(NKE_Free.eval (NKE_CommonProgram.run wr rr modelMerkle (finish fr) d pub proof ck hash none)).events,
  queryWindow (window rr fr loc nativeResume nativeMerkle d hash) observe e=e := by
  rw [NKE_CommonEval.source]
  exact observed_steps wr rr fr loc nativeResume nativeMerkle modelMerkle resumeProjection merkleProjection d pub proof ck hash headlineSize observe cuts
 have folded:=events_from_cuts _ (NKE_CommonProgram.run wr rr modelMerkle (finish fr) d pub proof ck hash none) before localSteps
 rw [NKE_CommonEval.source,NJU_CommonObserved.source] at folded
 exact folded
#print semantic_fold
#print axioms semantic_fold
end NLB_Parent
