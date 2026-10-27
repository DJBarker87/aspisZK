import XSa_ClaimY1
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSa_ClaimSelect
open AspisR1ClaimPreparedBridge

theorem all_six {S H : Type} (ops : AspisR1CurrentPreparedClaim.ClaimDotOps S)
 (sem : C.Sem H) (s : Slice U8) (point lane : Nat) (hp : point<6) (hl : lane<29) :
 mapR (fun q => toClaimQ (cq q)) (XRy_ClaimSelect.read (es sem) s point lane) =
 AspisR1CurrentPreparedClaim.ClaimScalar.read
   (AspisR1CurrentPreparedClaim.ClaimParser.withParser ops) (toClaimSem sem) s
   (XRn_Join_usize point) (XRn_Join_usize lane) := by
 by_cases hsmall : point<3
 · obtain ⟨q,hr,ht⟩ := XRy_ClaimSelectClaims.claims
     (AspisR1CurrentPreparedClaim.ClaimParser.withParser ops) sem s point lane hsmall hl
   rw [hr,map_ok,ht]
   rfl
 · have hs : point=3 ∨ point=4 ∨ point=5 := by omega
   rcases hs with hs | hs | hs
   · subst point
     obtain ⟨q,hr,ht⟩ := XRy_ClaimSelectExtra.extra
       (AspisR1CurrentPreparedClaim.ClaimParser.withParser ops) sem s lane hl
     rw [hr,map_ok]
     exact ht.symm
   · subst point
     obtain ⟨q,hr,ht⟩ := XRy_ClaimSelectExtra.before_z1
       (AspisR1CurrentPreparedClaim.ClaimParser.withParser ops) sem s lane hl
     rw [hr,map_ok]
     exact ht.symm
   · subst point
     exact XSa_ClaimY1.sixth ops sem s lane hl

#print axioms all_six
end XSa_ClaimSelect
