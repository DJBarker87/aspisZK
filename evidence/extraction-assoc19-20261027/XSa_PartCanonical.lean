import XSa_PartAssociation
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSa_PartCanonical
open AspisR1ClaimPreparedBridge

theorem canonical {H : Type} (D : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
 (sem : C.Sem H) (s : Slice U8) (g : Coeff) (hg : XSa_DotRun.canonical g)
 (point : Nat) (hp : point<6) (out : C.E)
 (hr : XRn_Join_preparedPart (es sem) s g point=ok (some out)) :
 XRy_WideMultiply.Canonical out := by
 have h := XSa_PartAssociation.part D sem s g hg point hp
 rw [hr,map_ok] at h
 have hc := AspisR1CurrentPreparedClaim.ClaimScalar.helper_return_canonical ops D
   (toClaimSem sem) s (arr toClaimE g) (XRn_Join_usize point) (toClaimE out)
   (fun state value hs => AspisR1S5ClaimScalarFinishCanonical.concrete_finishDot_success_canonical
     state AspisR1EbyKPushDecodedProductUpdate.QRaw value hs) h.symm
 exact hc

#print axioms canonical
end XSa_PartCanonical
