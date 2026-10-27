import XSa_ListClaimRaw
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotRun
set_option autoImplicit false
namespace XSa_ClaimRaw
abbrev Seven := XRy_ClaimSumStep.Seven
abbrev outcome := XSa_ListClaimRaw.outcome

theorem factor {H : Type} (D : C.D H) (sem : C.Sem H) (s : Slice U8)
 (inactive : C.E) (g : Coeff) (kappa : C.E) (k : Seven)
 (hp : XRn_Join_powers kappa 7 XRy_Powers.one=ok k.val) :
 XRo_Join_PreparedBoundaries.cachedClaim D sem s inactive g kappa =
 mapR outcome (do
   let xs ← XSa_OptionFold.run (XSa_PointList.step sem s g) (List.range 6) []
   XSa_PointList.finish inactive k xs) :=
 XSa_ListClaimRaw.factor D sem s inactive g kappa k.val hp

#print axioms factor
end XSa_ClaimRaw
