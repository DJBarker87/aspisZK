import S1ClosedPreparationInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim

theorem prepared_claim_digest_irrelevant {Dot H : Type} (ops : ClaimDotOps Dot)
    (first second : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (inactive : aspis_core.field.WideExact)
    (g : Array aspis_core.field.WideExact 29#usize) (kappa : aspis_core.field.WideExact) :
    verifier.prepared_claim ops first sem y1 inactive g kappa=
      verifier.prepared_claim ops second sem y1 inactive g kappa := by
  unfold verifier.prepared_claim verifier.prepared_claim_loop verifier.prepared_claim_loop.body
    verifier.prepared_claim_dot verifier.prepared_claim_dot_loop verifier.prepared_claim_dot_loop.body
  rfl

#print axioms prepared_claim_digest_irrelevant
end AspisR1CurrentPreparedClaim
namespace AspisR1ClaimPreparedBridge

theorem claimPublic_digest_irrelevant {H : Type}
    (first second : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive : PE) (g : Array PE 29#usize) (kappa : PE) :
    claimPublic first sem y1 inactive g kappa=claimPublic second sem y1 inactive g kappa := by
  unfold claimPublic
  rw [AspisR1CurrentPreparedClaim.prepared_claim_digest_irrelevant _ (toClaimDigest first) (toClaimDigest second)]

#print axioms claimPublic_digest_irrelevant
end AspisR1ClaimPreparedBridge
