import NHS_QueryPacket
import NHL_PreparedRecompose
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_PreparedPacket
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NFW_PreparedControl
open NHL_PreparedScalars NFN_LPi_FieldValues
theorem source (B : FinishModel.Boundaries)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
 (beforeSemantic : r1_wire.SemanticTranscript Unit) (challenges : r1_wire.Challenges)
 (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (sem : r1_semantic.Verified Unit)
 (semantic_finish : FinishModel.finish AspisS1ExtractedRoundChildren.children
   {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
   (NGQ_Effects.dictionary hashv) pub pre beforeSemantic challenges obs=ok (.Ok sem))
 (compact before y1 : Slice U8) (compact_length : compact.val.length=464)
 (before_length : before.val.length=928)
 (compact_check : NFU_Retarget.compact.check_values compact=ok (.Ok ()))
 (expansion : NFU_Retarget.LPn.Expand.NativeTrace compact.val before.val 29 y1.val)
 (v : verifier.View) (hash : Unit) (old : Scratch)
 (packet : NHL_OpeningPacket.Packet (NGQ_Effects.dictionary hashv) sem v hash)
 (same_y1 : v.y1=y1) (inactive_canonical : canonE (NFW_SampledDomains.toNative v.inactive))
 (qs : Array U32 22#usize) (afterQueries : transcript.Transcript Unit)
 (observed : NGP_L181.Observation NGQ_Effects.Reply)
 (cuts : NHK_Invocation.Cuts hashv packet.opening.transcript packet.opening.row v.final_message observed)
 (returned : observed.result=ok (.Ok qs,afterQueries))
 (rhoBlock : NGT_NBL_BlockTrace.Block (NGQ_Effects.dictionary hashv) afterQueries (NHL_OpeningPacket.nextRow packet.opening)
   PreparedScratchReachability.emptyPayload)
 (rho : aspis_core.field.QM31) (rhoReduction : NGT_Reduction.K rhoBlock.value rho) :
 ∃ g out, FIo_Native.weights.powers 29#usize (NFW_SampledDomains.toNative packet.opening.gamma)=ok g ∧
 canonE out ∧
 NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v hash old=
 ok (.Ok (PreparedScratchReachability.output sem v packet.opening.gamma packet.opening.kappa
   packet.opening.alpha rho qs (NFW_PowersCohort.toPublic out) {afterQueries with state:=rhoBlock.final}),
   NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g) := by
 have queries := (NHS_QueryPacket.source hashv sem v hash packet observed cuts).2.1.trans returned
 exact NHL_PreparedRecompose.source B (NGQ_Effects.dictionary hashv) pub pre beforeSemantic challenges obs sem
   semantic_finish compact before y1 compact_length before_length compact_check expansion v hash old packet
   same_y1 inactive_canonical qs afterQueries queries rhoBlock rho rhoReduction
#print axioms source
end AspisR1.NHS_PreparedPacket
