import NLB_Steps
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- C07 native-cut input family, indexed only by the actual source call. -/
def QueryCuts (wr rr fr : NP6_StdModel.Reservation) (modelMerkle : Merkle)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (observe : NKE_QueryInput.Args → QueryObservation) : Prop :=
 ∀ pr p a g geo pending reply,
 Event.query pr p a g geo pending reply∈(run wr rr modelMerkle (finish fr) d pub proof ck hash none).events →
 QueryCut ⟨pr,p,a,g,geo,pending⟩ (observe ⟨pr,p,a,g,geo,pending⟩)

theorem observed_steps (wr rr fr : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 (nativeResume : Resume) (nativeMerkle modelMerkle : Merkle)
 (resumeProjection : ResumeProjection wr nativeResume)
 (merkleProjection : MerkleProjection nativeMerkle modelMerkle)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (headlineSize : proof.val.length=57607)
 (observe : NKE_QueryInput.Args → QueryObservation)
 (cuts : QueryCuts wr rr fr modelMerkle d pub proof ck hash observe)
 (e : Event) (entered : e∈(run wr rr modelMerkle (finish fr) d pub proof ck hash none).events) :
 queryWindow (window rr fr loc nativeResume nativeMerkle d hash) observe e=e := by
 cases e with
 | query pr p a g geo pending r =>
   exact query_step wr rr fr loc nativeResume nativeMerkle modelMerkle d pub proof ck hash pr p a g geo pending r entered headlineSize observe (cuts pr p a g geo pending r entered)
 | resume c pr pu r => exact steps wr rr fr loc nativeResume nativeMerkle modelMerkle resumeProjection merkleProjection d pub proof ck hash _ entered
 | powers g r => exact steps wr rr fr loc nativeResume nativeMerkle modelMerkle resumeProjection merkleProjection d pub proof ck hash _ entered
 | inactive b r => exact steps wr rr fr loc nativeResume nativeMerkle modelMerkle resumeProjection merkleProjection d pub proof ck hash _ entered
 | merkle pr p root r => exact steps wr rr fr loc nativeResume nativeMerkle modelMerkle resumeProjection merkleProjection d pub proof ck hash _ entered
 | geometry qs n r => exact steps wr rr fr loc nativeResume nativeMerkle modelMerkle resumeProjection merkleProjection d pub proof ck hash _ entered
 | pending w r => exact steps wr rr fr loc nativeResume nativeMerkle modelMerkle resumeProjection merkleProjection d pub proof ck hash _ entered
 | flush b w r => exact steps wr rr fr loc nativeResume nativeMerkle modelMerkle resumeProjection merkleProjection d pub proof ck hash _ entered
 | finish v p a r => exact steps wr rr fr loc nativeResume nativeMerkle modelMerkle resumeProjection merkleProjection d pub proof ck hash _ entered
#print axioms observed_steps
end NLB_Parent
