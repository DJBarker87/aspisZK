import XRy_ClaimSelect
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XRy_ClaimSelectClaims
open AspisR1ClaimPreparedBridge

theorem claims {S H : Type} (ops : AspisR1CurrentPreparedClaim.ClaimDotOps S)
 (sem : C.Sem H) (y1 : Slice U8) (point lane : Nat) (hp : point<3) (hl : lane<29) :
 ∃ q : C.Q, XRy_ClaimSelect.read (es sem) y1 point lane = ok (eq q) ∧
 AspisR1CurrentPreparedClaim.ClaimScalar.read ops (toClaimSem sem) y1
   (XRn_Join_usize point) (XRn_Join_usize lane) = ok (toClaimQ q) := by
 let pi := XRn_Join_usize point
 let li := XRn_Join_usize lane
 have vp : pi.val=point := XRy_ClaimSelect.usize_value point (by omega)
 have vl : li.val=lane := XRy_ClaimSelect.usize_value lane (by omega)
 have hpi : pi.val<(3#usize).val := by scalar_tac
 have hli : li.val<(29#usize).val := by scalar_tac
 let row : Array C.Q 29#usize := sem.claims.val[pi.val]'(by rw [sem.claims.property]; exact hpi)
 let q : C.Q := row.val[li.val]'(by rw [row.property]; exact hli)
 refine ⟨q,?_,?_⟩
 · unfold XRy_ClaimSelect.read
   rw [if_pos hp]
   change (do
     let row ← Array.index_usize (arr (arr eq) sem.claims) pi
     Array.index_usize row li) = ok (eq q)
   rw [XRy_ArrayRead.mapped (arr eq) sem.claims pi hpi,bind_tc_ok]
   exact XRy_ArrayRead.mapped eq row li hli
 · unfold AspisR1CurrentPreparedClaim.ClaimScalar.read
   have hp2 : pi≤2#usize := by scalar_tac
   rw [if_pos hp2]
   change (do
     let row ← Array.index_usize (arr (arr toClaimQ) sem.claims) pi
     Array.index_usize row li) = ok (toClaimQ q)
   rw [XRy_ArrayRead.mapped (arr toClaimQ) sem.claims pi hpi,bind_tc_ok]
   exact XRy_ArrayRead.mapped toClaimQ row li hli

#print axioms claims
end XRy_ClaimSelectClaims
