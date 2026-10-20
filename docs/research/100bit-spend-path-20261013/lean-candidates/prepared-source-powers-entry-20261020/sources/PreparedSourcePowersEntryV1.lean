import PreparedSourcePowersJointRankV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1PreparedSourcePowersEntryV1
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1PublicPreparation AspisR1CurrentPreparedClaim.Concrete
open AspisR1PreparedSourcePowersBoundariesV1 AspisR1PreparedSourcePowersJointRankV1

/-- The extracted preparation entry forwards the scratch and preserves the
same original semantic payload sources in its claim/rank conclusion. -/
theorem entry_sourcePowers_original_payload_and_rank {H M Cv : Type} {L : Nat}
    (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (out : verifier.Prepared)
    (scratch scratchIn : Array AspisR1ClaimPreparedBridge.PE 29#usize)
    (hinactive : Canonical (toClaimE v.inactive))
    (h : PreparedScratchModel.entry (sourceBoundaries (installedBoundaries sampling embed))
      D sem v hash scratchIn=ok (.Ok out,scratch)) :
    (Canonical (toClaimE out.gamma) ∧ Canonical (toClaimE out.kappa)) ∧
    OriginalPayloadClaimMeaning sem v.y1 (toClaimE v.inactive)
      (toClaimE out.gamma) (toClaimE out.kappa) (toClaimE out.claim) (mapArray toClaimE scratch) ∧
    JointRankTrace sampling embed D p pubInput root length sem v hash out scratch := by
  have hp : PreparedScratchModel.prepare (sourceBoundaries (installedBoundaries sampling embed))
      D sem v hash scratchIn=ok (.Ok out,scratch) := by
    simpa only [PreparedScratchModel.entry] using h
  obtain ⟨⟨hcanonical,hclaim⟩,hrank⟩ := prepared_sourcePowers_claim_and_rank
    sampling embed D p pubInput root length sem v hash out scratch scratchIn hinactive hp
  obtain ⟨final,hzero,hvalues,hout,he⟩ := hclaim
  refine ⟨hcanonical,⟨final,hzero,?_,hout,he⟩,hrank⟩
  intro point hpoint
  obtain ⟨i,value,hi,xs,hinc,hcell,hlen,horder,hreads,hdecode⟩ := hvalues point hpoint
  refine ⟨i,value,hi,xs,hinc,hcell,hlen,horder,?_,hdecode⟩
  intro t ht
  exact ⟨selected_source_original_payload sem v.y1 point t.1 t.2.2 (hreads t ht).1,
    (hreads t ht).2⟩

#print axioms entry_sourcePowers_original_payload_and_rank
end AspisR1PreparedSourcePowersEntryV1
