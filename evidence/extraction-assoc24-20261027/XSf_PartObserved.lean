import XSf_DotObserved
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSf_PartObserved
open AspisR1ClaimPreparedBridge

theorem raw_reads {H : Type} (sem : C.Sem H) (s : Slice U8) (g : Coeff) (point : Nat)
 (out : C.E) (run : XRn_Join_preparedPart (es sem) s g point=ok (some out)) :
 ∀ n : Nat, n<29 → ∃ q : E.Q, XRy_ClaimSelect.read (es sem) s point n=ok q ∧ XSa_CheckedQ.valid q=true := by
 have he : XRn_Join_preparedPart (es sem) s g point =
   XSa_DotRun.run sem s g point 29 0#usize XRn_Join_dotZero XRn_Join_dotZero := by
   rw [XSa_PartFold.factor,XSa_PartRun.run sem s g point 29 0#usize XRn_Join_dotZero XRn_Join_dotZero (by scalar_tac)]
   rfl
 rw [he] at run
 intro n hn
 simpa only [show (0#usize).val=0 by scalar_tac,Nat.zero_add] using
   XSf_DotObserved.reads sem s g point 29 0#usize XRn_Join_dotZero XRn_Join_dotZero out (by scalar_tac) run n hn

theorem typed_reads {H : Type} (D : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
 (sem : C.Sem H) (s : Slice U8) (g : Coeff) (hg : canonical g) (point : Nat) (hp : point<6)
 (out : AspisR1CurrentPreparedClaim.Concrete.E)
 (run : AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot ops D (toClaimSem sem) s
   (arr toClaimE g) (XRn_Join_usize point)=ok (.Ok out)) :
 ∀ n : Nat, n<29 → ∃ q : E.Q, XRy_ClaimSelect.read (es sem) s point n=ok q ∧ XSa_CheckedQ.valid q=true := by
 have assoc := XSa_PartAssociation.part D sem s g hg point hp
 rw [run] at assoc
 cases hr : XRn_Join_preparedPart (es sem) s g point with
 | fail e => simp only [hr,map_fail] at assoc; cases assoc
 | div => simp only [hr,XRo_Join_ResultTransport.map_div] at assoc; cases assoc
 | ok opt =>
   cases opt with
   | none => simp only [hr,map_ok,outcome] at assoc; cases assoc
   | some value => exact raw_reads sem s g point value hr

#print axioms raw_reads
#print axioms typed_reads
end XSf_PartObserved
