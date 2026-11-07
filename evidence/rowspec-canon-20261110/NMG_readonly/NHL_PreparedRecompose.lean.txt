import NHL_OpeningPacket
import NHL_PreparedClaim
import NGN_EmittedEq
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_PreparedRecompose
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NFW_PreparedControl
open NHL_PreparedScalars NFN_LPi_FieldValues

/-- Query failure preserves incoming scratch and invokes no rho/powers/claim. -/
theorem query_error {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (old : Scratch)
 (packet : NHL_OpeningPacket.Packet D sem v hash) (e : verifier.Error) (after : transcript.Transcript H)
 (queries : actual.sampling.queries D packet.opening.transcript packet.opening.row v.final_message=ok (.Err e,after)) :
 NGN_Emitted.prepared actual D sem v hash old=ok (.Err e,old) := by
 rw [NGN_EmittedEq.staged,NHL_OpeningPacket.result D sem v hash packet,bind_tc_ok]
 exact NGN_FrameChain.query_exit actual D sem v old packet.opening e after queries

/-- Primitive opening, NGT rho, CLOSED powers and the NGY/NGU S8 packet are
actually substituted. The only OPEN callee law is `queries`, on the same
row/final_message/chronological state. All provenance inputs remain explicit. -/
theorem source (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
 (beforeSemantic : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
 (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (sem : r1_semantic.Verified H)
 (semantic_finish : FinishModel.finish AspisS1ExtractedRoundChildren.children
   {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
   D pub pre beforeSemantic challenges obs=ok (.Ok sem))
 (compact before y1 : Slice U8) (compact_length : compact.val.length=464)
 (before_length : before.val.length=928)
 (compact_check : NFU_Retarget.compact.check_values compact=ok (.Ok ()))
 (expansion : NFU_Retarget.LPn.Expand.NativeTrace compact.val before.val 29 y1.val)
 (v : verifier.View) (hash : H) (old : Scratch)
 (packet : NHL_OpeningPacket.Packet D sem v hash)
 (same_y1 : v.y1=y1) (inactive_canonical : canonE (NFW_SampledDomains.toNative v.inactive))
 (qs : Array U32 22#usize) (afterQueries : transcript.Transcript H)
 (queries : actual.sampling.queries D packet.opening.transcript packet.opening.row v.final_message=
   ok (.Ok qs,afterQueries))
 (rhoBlock : NGT_NBL_BlockTrace.Block D afterQueries (NHL_OpeningPacket.nextRow packet.opening)
   PreparedScratchReachability.emptyPayload)
 (rho : aspis_core.field.QM31) (rhoReduction : NGT_Reduction.K rhoBlock.value rho) :
 ∃ g out, FIo_Native.weights.powers 29#usize (NFW_SampledDomains.toNative packet.opening.gamma)=ok g ∧
 canonE out ∧
 NGN_Emitted.prepared actual D sem v hash old=
 ok (.Ok (PreparedScratchReachability.output sem v packet.opening.gamma packet.opening.kappa
   packet.opening.alpha rho qs (NFW_PowersCohort.toPublic out) {afterQueries with state:=rhoBlock.final}),
   NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g) := by
 have gammaCanonical := NHL_OpeningPacket.gamma_canonical D sem v hash packet
 have kappaCanonical := NHL_OpeningPacket.kappa_canonical D sem v hash packet
 obtain ⟨g,powers,powersPublic,gCanonical⟩ := NFW_PowersCohort.source 29#usize
   (NFW_SampledDomains.toNative packet.opening.gamma) gammaCanonical
 rw [NFW_SampledDomains.roundtrip] at powersPublic
 obtain ⟨out,canonical,claim⟩ := NHL_PreparedClaim.claim B D pub pre beforeSemantic challenges obs sem
   semantic_finish compact before y1 compact_length before_length compact_check expansion
   (NFW_SampledDomains.toNative packet.opening.gamma) (NFW_SampledDomains.toNative v.inactive)
   (NFW_SampledDomains.toNative packet.opening.kappa) gammaCanonical inactive_canonical kappaCanonical
   g powers v packet.opening qs rho {afterQueries with state:=rhoBlock.final} same_y1
   (NFW_SampledDomains.roundtrip v.inactive).symm (NFW_SampledDomains.roundtrip packet.opening.kappa).symm
 refine ⟨g,out,powers,canonical,?_⟩
 rw [NGN_EmittedEq.staged,NHL_OpeningPacket.result D sem v hash packet,bind_tc_ok]
 rw [NGN_FrameChain.query_rho actual D sem v old packet.opening qs afterQueries queries]
 rw [NHL_PreparedScalars.rho D sem v packet.opening qs afterQueries _
   (NHL_OpeningPacket.increment D sem v hash packet) rhoBlock rho rhoReduction]
 rw [NGN_FrameChain.powers_claim actual D sem v packet.opening qs rho _
   (NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g) powersPublic]
 exact claim
#print axioms query_error
#print axioms source
end AspisR1.NHL_PreparedRecompose
