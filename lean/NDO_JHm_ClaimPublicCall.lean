import NDO_JHl_ClaimReached
set_option autoImplicit false
namespace AspisR1.JHm_ClaimPublicCall
open Aeneas Aeneas.Std Result AspisR1ClaimPreparedBridge

theorem source {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive kappa claim : PE) (g : Array PE 29#usize)
    (call : claimPublic D sem y1 inactive g kappa=ok (.Ok claim)) :
    ∃ out,AspisR1CurrentPreparedClaim.verifier.prepared_claim JGi_DotOps.ops (toClaimDigest D)
      (toClaimSem sem) y1 (toClaimE inactive) (mapArray toClaimE g) (toClaimE kappa)=ok (.Ok out) ∧
      fromClaimE out=claim := by
  unfold claimPublic at call
  obtain ⟨r,run,returned⟩ := Port3_PushFrame.bind_success _ _ _ call
  cases r with
  | Err e => cases returned
  | Ok out => exact ⟨out,run,core.result.Result.Ok.inj (Result.ok.inj returned)⟩
#print axioms source
end AspisR1.JHm_ClaimPublicCall
