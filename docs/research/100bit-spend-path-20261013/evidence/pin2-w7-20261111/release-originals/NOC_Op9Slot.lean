import NOC_FinishSource
import NNV_SemanticPrefix
import NNV_PreparedAtHost
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

/-- Full verify-prefix Result at the installed finish, from the SAME
returned observed value: parse, public transcript, begin, then the fixed
finish of NOC_FinishSource.source. -/
theorem prefix_finish (pub : NNH_Libraries.VL.Public) (bytes : Slice U8) (env : RSL.Env)
 (sem : RSL.Verified NNH_Libraries.VL)
 (called : NNH_ObservedReturns.value ⟨pub, LIB_Carriers.bytes bytes⟩ env = .ok sem) :
 AspisR1PublicPreparation.VerifyPrefix.verify
  (AspisR1PublicPreparation.FinishModel.finish AspisS1ExtractedRoundChildren.children NOC_FinishSource.Bi)
  (LIB_VCode.digest env) pub bytes () none =
 .ok (.Ok (LIBC_PreparedCarriers.verified LIB_Prepared.types sem)) := by
 obtain ⟨p, parsed, initialized, begun⟩ := NNV_SemanticPrefix.returned pub bytes env sem called
 have fin := NOC_FinishSource.source ⟨pub, p.prefix_, p.before, p.challenges⟩ env sem p.finished
 have hk : LIB_Env.nativeKey (LIB_VCarriers.c1Root p.prefix_) =
   (LIB_VCarriers.prefixRaw p.prefix_).c1_root := NNX_RootCopy.key _
 have pt : AspisR1PublicPreparation.r1_semantic.public_transcript (LIB_VCode.digest env) pub ()
   (LIB_VCarriers.prefixRaw p.prefix_).c1_root = .ok (.Ok p.initial) := by
  rw [← hk]; exact initialized
 unfold AspisR1PublicPreparation.VerifyPrefix.verify
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
#print axioms prefix_finish
end AspisR1.NOC_Op9Slot
end
