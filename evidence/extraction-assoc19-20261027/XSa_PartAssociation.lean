import XSa_PartRun
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSa_PartAssociation
open AspisR1ClaimPreparedBridge

theorem part {H : Type} (D : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
 (sem : C.Sem H) (s : Slice U8) (g : Coeff) (hg : canonical g) (point : Nat) (hp : point<6) :
 mapR outcome (XRn_Join_preparedPart (es sem) s g point) =
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot ops D (toClaimSem sem) s
   (arr toClaimE g) (XRn_Join_usize point) := by
 have hr := XSa_PartRun.run sem s g point 29 0#usize XRn_Join_dotZero XRn_Join_dotZero (by scalar_tac)
 have he : XRn_Join_preparedPart (es sem) s g point =
   XSa_DotRun.run sem s g point 29 0#usize XRn_Join_dotZero XRn_Join_dotZero := by
   rw [XSa_PartFold.factor,hr]
   rfl
 rw [he]
 exact XSa_ClaimDot.dot D sem s g hg point hp

#print axioms part
end XSa_PartAssociation
