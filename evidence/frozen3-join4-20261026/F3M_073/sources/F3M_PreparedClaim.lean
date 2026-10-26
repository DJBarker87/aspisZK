import F3M_InactiveCanonical
import PAln_Borrowed
import CurrentPreparedInstalledMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_PreparedClaim
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open OriginalSerializerInstallation

theorem original {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (proof semantic y1 : Slice U8) (v : verifier.View) (hash : H)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (out : verifier.Prepared)
    (view : sourceView proof semantic y1=ok (.Ok v))
    (success : originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
      D sem v hash input=ok (.Ok out,scratch)) :
    ∃ (retained : AspisR1PublicPreparation.verifier.Prepared)
      (rs : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize),
      currentPrepared retained=out ∧ AspisR1ClaimPreparedBridge.mapArray currentE rs=scratch ∧
      AspisR1ClaimPreparedBridge.OriginalPayloadClaimMeaning (retainedSem sem) (retainedView v).y1
        (AspisR1ClaimPreparedBridge.toClaimE (retainedView v).inactive)
        (AspisR1ClaimPreparedBridge.toClaimE retained.gamma)
        (AspisR1ClaimPreparedBridge.toClaimE retained.kappa)
        (AspisR1ClaimPreparedBridge.toClaimE retained.claim)
        (AspisR1ClaimPreparedBridge.mapArray AspisR1ClaimPreparedBridge.toClaimE rs) := by
  obtain ⟨retained,rs,prepared,same,carried⟩ := PAln_Borrowed.original_success
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed D sem v hash input scratch out success
  have canonical := F3M_InactiveCanonical.source proof semantic y1 v view
  have meaning := AspisR1ClaimPreparedBridge.InstalledMeaning.prepared_installed_meaning
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed (retainedDigest D)
    (retainedSem sem) (retainedView v) hash retained rs (AspisR1ClaimPreparedBridge.mapArray retainedE input)
    canonical prepared
  exact ⟨retained,rs,same,carried,meaning.2.2.1⟩

#print axioms original
end AspisR1.F3M_PreparedClaim
end
