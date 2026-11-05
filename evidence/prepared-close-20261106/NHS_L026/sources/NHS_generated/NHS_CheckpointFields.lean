import NHS_PreparedPacket
import NHS_SemanticFields
import NHS_InvocationBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_CheckpointFields
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NFW_PreparedControl
open NHL_PreparedScalars NFN_LPi_FieldValues
theorem source (B : FinishModel.Boundaries)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
 (beforeSemantic : r1_wire.SemanticTranscript Unit) (challenges : r1_wire.Challenges)
 (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (sem : r1_semantic.Verified Unit)
 (semantic_finish : FinishModel.finish AspisS1ExtractedRoundChildren.children
   {F3M_CircleSource.install B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
   (NGQ_Effects.dictionary hashv) pub pre beforeSemantic challenges obs=ok (.Ok sem))
 (compact before y1 : Slice U8) (compact_length : compact.val.length=464)
 (before_length : before.val.length=928)
 (compact_check : NFU_Retarget.compact.check_values compact=ok (.Ok ()))
 (expansion : NFU_Retarget.LPn.Expand.NativeTrace compact.val before.val 29 y1.val)
 (v : verifier.View) (hash : Unit) (old : Scratch)
 (packet : NHL_OpeningPacket.Packet (NGQ_Effects.dictionary hashv) sem v hash)
 (same_y1 : v.y1=y1) (inactive_canonical : canonE (NFW_SampledDomains.toNative v.inactive))
 (variant : v.variant=.S2)
 (qs : Array U32 22#usize) (afterQueries : transcript.Transcript Unit)
 (observed : NGP_L181.Observation NGQ_Effects.Reply)
 (cuts : NHK_Invocation.Cuts hashv packet.opening.transcript packet.opening.row v.final_message observed)
 (returned : observed.result=ok (.Ok qs,afterQueries))
 (rhoBlock : NGT_NBL_BlockTrace.Block (NGQ_Effects.dictionary hashv) afterQueries (NHL_OpeningPacket.nextRow packet.opening)
   PreparedScratchReachability.emptyPayload)
 (rho : aspis_core.field.QM31) (rhoReduction : NGT_Reduction.K rhoBlock.value rho) :
 ∃ g out,
 let p := PreparedScratchReachability.output sem v packet.opening.gamma packet.opening.kappa
   packet.opening.alpha rho qs (NFW_PowersCohort.toPublic out) {afterQueries with state:=rhoBlock.final}
 let scratch := NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g
 FIo_Native.weights.powers 29#usize (NFW_SampledDomains.toNative packet.opening.gamma)=ok g ∧
 canonE out ∧
 NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v hash old=ok (.Ok p,scratch) ∧
 NGC_PreparationBoundary.Fields (NFW_PreparedPort.prepared p) ∧
 NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray (NFW_PreparedPort.map NFW_PreparedPort.e scratch)) := by
 obtain ⟨g,out,powers,canonical,run⟩ := NHS_PreparedPacket.source (F3M_CircleSource.install B)
   hashv pub pre beforeSemantic challenges obs sem semantic_finish compact before y1 compact_length
   before_length compact_check expansion v hash old packet same_y1 inactive_canonical qs afterQueries
   observed cuts returned rhoBlock rho rhoReduction
 let p := PreparedScratchReachability.output sem v packet.opening.gamma packet.opening.kappa
   packet.opening.alpha rho qs (NFW_PowersCohort.toPublic out) {afterQueries with state:=rhoBlock.final}
 let scratch := NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g
 have produced := NHS_ProducedCanonical.source (NGQ_Effects.dictionary hashv) sem v hash old scratch p run
 have semantic := NHS_SemanticFields.source AspisS1ExtractedRoundChildren.children
   {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
   (NGQ_Effects.dictionary hashv) pub pre beforeSemantic challenges obs sem semantic_finish
 have bounded := NHS_InvocationBounds.source hashv packet.opening.transcript packet.opening.row
   v.final_message observed cuts qs afterQueries returned
 refine ⟨g,out,powers,canonical,run,?_,produced.2.2.2.2⟩
 exact NHS_Fields.transport p variant bounded produced.1 produced.2.1 produced.2.2.1
   produced.2.2.2.1 semantic.1 semantic.2 (NHS_CanonicalPorts.claim out canonical)
#print axioms source
end AspisR1.NHS_CheckpointFields
