import XSa_DotLoop
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSa_ClaimDot
open AspisR1ClaimPreparedBridge

theorem dot {H : Type} (D : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
 (sem : C.Sem H) (s : Slice U8) (g : Coeff) (hg : canonical g) (point : Nat) (hp : point<6) :
 mapR outcome (run sem s g point 29 0#usize XRn_Join_dotZero XRn_Join_dotZero) =
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot ops D (toClaimSem sem) s
   (arr toClaimE g) (XRn_Join_usize point) := by
 unfold AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot
 rw [new_dot,bind_tc_ok]
 exact XSa_DotLoop.paired D sem s g hg point hp 29 ⟨0#usize,29#usize⟩
   XRn_Join_dotZero XRn_Join_dotZero (by scalar_tac) (by scalar_tac)

#print axioms dot
end XSa_ClaimDot
