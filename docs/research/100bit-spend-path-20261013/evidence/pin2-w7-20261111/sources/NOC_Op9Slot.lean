import NOC_FinishSource
import NNV_SemanticPrefix
import NNV_PreparedAtHost
import NJG_ObservedInstall
import RPz7_S1SemanticCurrentCodeV1
/-! PIN2 W10 (2026-11-11), coordinator-approved: `prefix_finish` is restated over
`NJG_ObservedInstall.prefixPIN2` (the frozen `VerifyPrefix.verify` text with its single
public-transcript call replaced by the erased `S1SemanticCode.publicTranscriptPIN2`), with the SAME
arguments, frozen carriers and the SAME conclusion value
`.ok (.Ok (LIBC_PreparedCarriers.verified LIB_Prepared.types sem))` (release: left-hand side
`VerifyPrefix.verify ..`).  Its public-transcript step comes from the PIN2-on-copies conjunct of the
restated `NNV_SemanticPrefix.returned` through `publicTranscriptPIN2_erasure`.
NEW `installed_verify`: `S1SemanticInstallation.verify` (W7: the PIN2 VerifyPrefix on the copies)
equals the release body shape with `prefixPIN2` in place of `VerifyPrefix.verify`
(via W7 `S1SemanticCodeInstallation.source` and W9 `prefixPIN2_erasure`), so NOC_Op9 and
NOC_SemConv rewrite with it instead of unfolding the definition.
`slot`, `digest`, `pub_round`, `reservation` unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_Op9Slot
open Aeneas Aeneas.Std Result NNH_Run5bCtx AspisR1CurrentCaller

/-- The literal installed op9 slot at the host configuration, on release
`none`: the semantic verify over the Claims-unrolled deployed boundaries. -/
theorem slot {W Tx : Type} (c : Ctx W Tx) (D : aspis_core.digest.Digest32 Unit)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) :
 (DrvC_Installation.currentInstalled (configuration c)).op9 D pub bytes () none =
 S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
  (ClaimsUnrolledFinish.install (NP6_StdModel.calls c.fixed.reservation)
   (IDa_Deployed.boundaries c.fixed.reservation)) D pub bytes () := rfl

/-- The retained host digest is the library digest at the SAME environment. -/
theorem digest {W Tx : Type} (c : Ctx W Tx) :
 InstalledPreparation.retainedDigest (NNV_PreparedAtHost.digest c) = LIB_VCode.digest (envOf c) := rfl

theorem pub_round (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public) :
 FirstComposition.toRetainedPublic (FirstComposition.toCurrentPublic pub) = pub := by
 cases pub <;> rfl

theorem reservation {W Tx : Type} (c : Ctx W Tx) (h : (envOf c).reservation = true) :
 c.fixed.reservation = .Ok () := (NNH_HostEnv.reserveOK_iff _).1 h

/-- The installed semantic verify (W7: PIN2 VerifyPrefix on the copies) in the release body
shape, with `NJG_ObservedInstall.prefixPIN2` in place of the frozen `VerifyPrefix.verify`. -/
theorem installed_verify (R : AspisR1PublicPreparation.RoundModel.Boundaries)
 (B : AspisR1PublicPreparation.FinishModel.Boundaries)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) :
 S1SemanticInstallation.verify R B D pub bytes hash =
 (do
  let result ← NJG_ObservedInstall.prefixPIN2
   (AspisR1PublicPreparation.FinishModel.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B))
   (InstalledPreparation.retainedDigest D) (FirstComposition.toRetainedPublic pub) bytes hash none
  ok (match result with
   | .Ok sem => .Ok (S1SemanticCarrier.currentSem sem)
   | .Err error => .Err (S1SemanticCarrier.currentWireError error))) := by
 rw [←S1SemanticCodeInstallation.source]
 unfold S1SemanticCodeInstallation.code
 rw [AspisR1PublicPreparation.PreparedHashCode.erase_bind,NJG_ObservedInstall.prefixPIN2_erasure]
 apply congrArg (fun k => _ >>= k)
 funext result
 rw [AspisR1PublicPreparation.PreparedHashCode.erase_pure]
 cases result <;> rfl

/-- Full verify-prefix Result at the installed finish, from the SAME
returned observed value: parse, public transcript (PIN2), begin, then the fixed
finish of NOC_FinishSource.source. -/
theorem prefix_finish (pub : NNH_Libraries.VL.Public) (bytes : Slice U8) (env : RSL.Env)
 (sem : RSL.Verified NNH_Libraries.VL)
 (called : NNH_ObservedReturns.value ⟨pub, LIB_Carriers.bytes bytes⟩ env = .ok sem) :
 NJG_ObservedInstall.prefixPIN2
  (AspisR1PublicPreparation.FinishModel.finish AspisS1ExtractedRoundChildren.children NOC_FinishSource.Bi)
  (LIB_VCode.digest env) pub bytes () none =
 .ok (.Ok (LIBC_PreparedCarriers.verified LIB_Prepared.types sem)) := by
 obtain ⟨p, parsed, initialized, begun⟩ := NNV_SemanticPrefix.returned pub bytes env sem called
 have fin := NOC_FinishSource.source ⟨pub, p.prefix_, p.before, p.challenges⟩ env sem p.finished
 have hk : LIB_Env.nativeKey (LIB_VCarriers.c1Root p.prefix_) =
   (LIB_VCarriers.prefixRaw p.prefix_).c1_root := NNX_RootCopy.key _
 have pt : AspisR1PublicPreparation.PreparedHashCode.erase
   (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 (LIB_VCode.digest env) pub ()
    (LIB_VCarriers.prefixRaw p.prefix_).c1_root) = .ok (.Ok p.initial) := by
  rw [AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2_erasure, ← hk]
  exact (congrArg (AspisR1PublicPreparation.PIN2W7_PrefixGlue.rmap
    (AspisR1PublicPreparation.PIN2W7_PrefixGlue.cres AspisR1PublicPreparation.PIN2W7_PrefixGlue.transcriptBack
      AspisR1PublicPreparation.PIN2W7_PrefixGlue.errorBack)) initialized).trans rfl
 unfold NJG_ObservedInstall.prefixPIN2
 noc_stp parsed
 noc_nrm
 noc_stp pt
 noc_nrm
 noc_stp begun
 noc_nrm
 exact fin
#print axioms slot
#print axioms digest
#print axioms pub_round
#print axioms reservation
#print axioms installed_verify
#print axioms prefix_finish
end AspisR1.NOC_Op9Slot
end
