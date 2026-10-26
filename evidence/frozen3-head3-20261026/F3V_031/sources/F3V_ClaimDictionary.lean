import S1ClosedPreparationInstallationV1
set_option autoImplicit false
namespace AspisR1.F3V_ClaimDictionary
open Aeneas Aeneas.Std Result

theorem current {Dot Hash : Type} (ops : AspisR1CurrentPreparedClaim.ClaimDotOps Dot)
    (first second : AspisR1CurrentPreparedClaim.aspis_core.Digest32 Hash)
    (sem : AspisR1CurrentPreparedClaim.r1_semantic.Verified Hash) (y1 : Slice U8)
    (inactive : AspisR1CurrentPreparedClaim.aspis_core.field.WideExact)
    (g : Array AspisR1CurrentPreparedClaim.aspis_core.field.WideExact 29#usize)
    (kappa : AspisR1CurrentPreparedClaim.aspis_core.field.WideExact) :
    AspisR1CurrentPreparedClaim.verifier.prepared_claim ops first sem y1 inactive g kappa=
      AspisR1CurrentPreparedClaim.verifier.prepared_claim ops second sem y1 inactive g kappa := by
  unfold AspisR1CurrentPreparedClaim.verifier.prepared_claim
    AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop
    AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body
    AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot
    AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot_loop
    AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot_loop.body
  rfl

#print axioms current
end AspisR1.F3V_ClaimDictionary
