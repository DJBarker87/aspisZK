import SelectedWideViewInactiveV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1SelectedWideViewV1
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete
open AspisR1PreparedSourcePowersBoundariesV1 AspisR1PreparedSourcePowersJointRankV1

def preparedView (v : verifier.View) : AspisR1PublicPreparation.verifier.View :=
  { variant := match v.variant with
      | .S1 => .S1 | .S2 => .S2 | .D => .D,
    semantic := v.semantic,y1 := v.y1,inactive := prepCarrier v.inactive,
    round0 := v.round0,folded_root := v.folded_root,round1 := v.round1,
    final_message := v.final_message,query_bytes := v.query_bytes }

theorem selected_view_preparation_original_payload_and_rank {H M Cv : Type} {L : Nat}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : Array U8 32#usize) (length : U32)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (proof semantic y1 : Slice U8) (v : verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (scratch scratchIn : Array AspisR1ClaimPreparedBridge.PE 29#usize)
    (hview : verifier.candidate.wide_view proof semantic y1=ok (.Ok v))
    (h : AspisR1PublicPreparation.PreparedScratchModel.entry
      (sourceBoundaries (installedBoundaries sampling embed))
      D sem (preparedView v) hash scratchIn=ok (.Ok out,scratch)) :
    (Canonical (toClaimE out.gamma) ∧ Canonical (toClaimE out.kappa)) ∧
    OriginalPayloadClaimMeaning sem v.y1 (toClaimE (prepCarrier v.inactive))
      (toClaimE out.gamma) (toClaimE out.kappa) (toClaimE out.claim) (mapArray toClaimE scratch) ∧
    JointRankTrace sampling embed D p pubInput root length sem (preparedView v) hash out scratch := by
  exact AspisR1PreparedSourcePowersEntryV1.entry_sourcePowers_original_payload_and_rank
    sampling embed D p pubInput root length sem (preparedView v) hash out scratch scratchIn
    (wide_view_inactive_canonical proof semantic y1 v hview) h

#print axioms selected_view_preparation_original_payload_and_rank
end AspisR1SelectedWideViewV1
