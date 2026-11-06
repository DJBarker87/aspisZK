import NLB_QueryWindow
import NLB_C07
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Install C07's decoded native arguments and complete return into the SAME
parent step. All width/domain facts follow from that source prefix. The native
frame cut is explicit; no source/native log equality is a hypothesis. -/
theorem query_step (wr rr fr : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 (nativeResume : Resume) (nativeMerkle modelMerkle : Merkle)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (proofArg : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (reply : R (verifier.Accumulator × verifier.BatchedWeights))
 (entered : Event.query proofArg p a g geometry pending reply∈
  (run wr rr modelMerkle (finish fr) d pub proof ck hash none).events)
 (headlineSize : proof.val.length=57607)
 (observe : NKE_QueryInput.Args → QueryObservation)
 (cut : QueryCut ⟨proofArg,p,a,g,geometry,pending⟩ (observe ⟨proofArg,p,a,g,geometry,pending⟩)) :
 queryWindow (window rr fr loc nativeResume nativeMerkle d hash) observe
  (.query proofArg p a g geometry pending reply)=.query proofArg p a g geometry pending reply := by
 obtain ⟨proofEq,_,_,_,_,weights,raw,inverses,lines,_⟩ :=
  NKO_C07.at_actual wr rr modelMerkle (finish fr) d pub proof ck hash proofArg p a g geometry pending reply entered
 let before : NKE_QueryInput.Args := ⟨proofArg,p,a,g,geometry,pending⟩
 let o := observe before
 have same : queryArgs before o=before := by
  apply NKO_FrameG.args_source o.written o.heap o.logBase o.logSize o.proofBase before o.args
  · exact cut.1
  · exact cut.2.1
  · change proofArg.val.length=57607
    rw [proofEq,headlineSize]
  · exact weights
  · exact inverses
  · exact lines
  · exact raw
  · exact cut.2.2.1
  · exact cut.2.2.2.1
  · exact cut.2.2.2.2.1
  · exact cut.2.2.2.2.2.1
  · exact cut.2.2.2.2.2.2.1
  · exact cut.2.2.2.2.2.2.2.1
  · exact cut.2.2.2.2.2.2.2.2
 change Event.query (queryArgs before o).proof (queryArgs before o).prepared
  (queryArgs before o).accumulator (queryArgs before o).powers
  (queryArgs before o).geometry (queryArgs before o).pending
  (NKO_QueryReturnG.G (NKE_QueryReturn.observed (NKE_QueryInput.child (queryArgs before o))))=_
 rw [same]
 exact C07_step wr rr fr loc nativeResume nativeMerkle modelMerkle d pub proof ck hash proofArg p a g geometry pending reply entered
#print axioms query_step
end NLB_Parent
