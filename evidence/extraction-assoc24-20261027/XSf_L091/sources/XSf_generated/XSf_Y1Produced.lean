import XSf_DotObserved
import XSf_LaneDomain
import XSf_ReachedScratch
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XRk_ResultTools XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSf_Y1Produced
open AspisR1 AspisR1ClaimPreparedBridge

theorem part_lanes {H : Type} (sem : C.Sem H) (s : Slice U8) (g : Coeff) (out : C.E)
 (run : XRn_Join_preparedPart (es sem) s g 5=ok (some out)) :
 ∀ n : Nat, n<29 → ∃ x : C.E, XSa_ParserLane.field s n=ok x := by
 have he : XRn_Join_preparedPart (es sem) s g 5 =
   XSa_DotRun.run sem s g 5 29 0#usize XRn_Join_dotZero XRn_Join_dotZero := by
   rw [XSa_PartFold.factor,XSa_PartRun.run sem s g 5 29 0#usize XRn_Join_dotZero XRn_Join_dotZero (by scalar_tac)]
   rfl
 rw [he] at run
 intro n hn
 obtain ⟨q,hq,hv⟩ := XSf_DotObserved.reads sem s g 5 29 0#usize XRn_Join_dotZero XRn_Join_dotZero out (by scalar_tac) run n hn
 have hread : XRy_ClaimSelect.read (es sem) s 5 n=ok q := by simpa only [show (0#usize).val=0 by scalar_tac,Nat.zero_add] using hq
 have hy := XSa_ClaimY1.raw sem s n
 rw [hread,map_ok] at hy
 obtain ⟨x,hx,_⟩ := bind_success _ _ _ hy.symm
 exact ⟨x,hx⟩

theorem dot_domain {H : Type} (D : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
 (sem : C.Sem H) (s : Slice U8) (g : Coeff) (hg : canonical g)
 (out : AspisR1CurrentPreparedClaim.Concrete.E)
 (run : AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot ops D (toClaimSem sem) s
   (arr toClaimE g) 5#usize=ok (.Ok out)) : LPq_SelectedDomain.ByteDomain s := by
 have assoc := XSa_PartAssociation.part D sem s g hg 5 (by omega)
 have five : XRn_Join_usize 5=5#usize := by apply UScalar.eq_of_val_eq; rfl
 rw [five,run] at assoc
 cases hr : XRn_Join_preparedPart (es sem) s g 5 with
 | fail e => simp only [hr,map_fail] at assoc; cases assoc
 | div => simp only [hr,XRo_Join_ResultTransport.map_div] at assoc; cases assoc
 | ok opt =>
   cases opt with
   | none => simp only [hr,map_ok,outcome] at assoc; cases assoc
   | some value => exact XSf_LaneDomain.from_lanes s (part_lanes sem s g value hr)

#print axioms part_lanes
#print axioms dot_domain
end XSf_Y1Produced
