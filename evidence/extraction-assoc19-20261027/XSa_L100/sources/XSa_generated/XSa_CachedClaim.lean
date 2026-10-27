import XSa_ClaimRaw
import XSa_ClaimInitial
import XSa_PointLoop
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSa_CachedClaim
open AspisR1ClaimPreparedBridge

def back : core.result.Result AspisR1CurrentPreparedClaim.Concrete.E AspisR1CurrentPreparedClaim.verifier.Error →
 core.result.Result C.E C.Err
 | .Ok x => .Ok (fromClaimE x)
 | .Err e => .Err (fromClaimError e)

theorem claim {H : Type} (D : C.D H) (sem : C.Sem H) (s : Slice U8)
 (inactive kappa : C.E) (g : Coeff)
 (hi : XRy_WideMultiply.Canonical inactive) (hkappa : XRy_WideMultiply.Canonical kappa)
 (hg : canonical g) :
 XRo_Join_PreparedBoundaries.cachedClaim D sem s inactive g kappa =
 XRo_Join_Installed.actual.claim D sem s inactive g kappa := by
 obtain ⟨k,hlist,hpowers,hk⟩ := XSa_PowersDimensions.seven kappa hkappa
 let parts := XSa_ClaimInitial.initial inactive
 let raw := XSa_PointRun.run sem s g k 6 0#usize parts
 have hpoints : raw = (do
   let xs ← XSa_OptionFold.run (XSa_PointList.step sem s g) (List.range 6) []
   XSa_PointList.finish inactive k xs) :=
   XSa_PointList.paired sem s g k inactive 6 0#usize parts []
     (by scalar_tac) (XSa_ClaimInitial.front inactive)
 have hraw : XRo_Join_PreparedBoundaries.cachedClaim D sem s inactive g kappa=
   mapR XSa_ClaimRaw.outcome raw := by
   rw [XSa_ClaimRaw.factor D sem s inactive g kappa k hlist,←hpoints]
 have ht : mapR XSa_DotRun.outcome raw =
   AspisR1CurrentPreparedClaim.verifier.prepared_claim ops (toClaimDigest D) (toClaimSem sem) s
     (toClaimE inactive) (arr toClaimE g) (toClaimE kappa) := by
   unfold AspisR1CurrentPreparedClaim.verifier.prepared_claim
   rw [hpowers,bind_tc_ok]
   dsimp only
   rw [XSa_ClaimInitial.actual,bind_tc_ok]
   exact XSa_PointLoop.paired (toClaimDigest D) sem s g hg k hk 6 ⟨0#usize,6#usize⟩ parts
     (XSa_ClaimInitial.canonical inactive hi) (by scalar_tac) (by scalar_tac)
 rw [hraw,XRo_Join_Installed.cached_claim_slot]
 change mapR XSa_ClaimRaw.outcome raw =
   mapR back (AspisR1CurrentPreparedClaim.verifier.prepared_claim ops (toClaimDigest D) (toClaimSem sem) s
     (toClaimE inactive) (arr toClaimE g) (toClaimE kappa))
 rw [←ht,map_comp]
 cases raw with
 | fail e => rfl
 | div => rfl
 | ok opt => cases opt <;> rfl

#print axioms claim
end XSa_CachedClaim
