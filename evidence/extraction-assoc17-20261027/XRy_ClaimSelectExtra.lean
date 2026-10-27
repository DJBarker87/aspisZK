import XRy_ClaimSelectClaims
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XRy_ClaimSelectExtra
open AspisR1ClaimPreparedBridge

theorem extra {S H : Type} (ops : AspisR1CurrentPreparedClaim.ClaimDotOps S)
 (sem : C.Sem H) (y1 : Slice U8) (lane : Nat) (hl : lane<29) :
 ∃ q : C.Q, XRy_ClaimSelect.read (es sem) y1 3 lane = ok (eq q) ∧
 AspisR1CurrentPreparedClaim.ClaimScalar.read ops (toClaimSem sem) y1
   3#usize (XRn_Join_usize lane) = ok (toClaimQ q) := by
 let li := XRn_Join_usize lane
 have vl : li.val=lane := XRy_ClaimSelect.usize_value lane (by omega)
 have hli : li.val<(29#usize).val := by scalar_tac
 let q : C.Q := sem.extra.val[li.val]'(by rw [sem.extra.property]; exact hli)
 refine ⟨q,?_,?_⟩
 · exact XRy_ArrayRead.mapped eq sem.extra li hli
 · unfold AspisR1CurrentPreparedClaim.ClaimScalar.read
   have hp : ¬3#usize≤2#usize := by scalar_tac
   have hv : (3#usize).val=3 := by scalar_tac
   simp only [if_neg hp,hv]
   exact XRy_ArrayRead.mapped toClaimQ sem.extra li hli

theorem before_z1 {S H : Type} (ops : AspisR1CurrentPreparedClaim.ClaimDotOps S)
 (sem : C.Sem H) (y1 : Slice U8) (lane : Nat) (hl : lane<29) :
 ∃ q : C.Q, XRy_ClaimSelect.read (es sem) y1 4 lane = ok (eq q) ∧
 AspisR1CurrentPreparedClaim.ClaimScalar.read ops (toClaimSem sem) y1
   4#usize (XRn_Join_usize lane) = ok (toClaimQ q) := by
 let li := XRn_Join_usize lane
 have vl : li.val=lane := XRy_ClaimSelect.usize_value lane (by omega)
 have hli : li.val<(29#usize).val := by scalar_tac
 let q : C.Q := sem.before_z1.val[li.val]'(by rw [sem.before_z1.property]; exact hli)
 refine ⟨q,?_,?_⟩
 · exact XRy_ArrayRead.mapped eq sem.before_z1 li hli
 · unfold AspisR1CurrentPreparedClaim.ClaimScalar.read
   have hp : ¬4#usize≤2#usize := by scalar_tac
   have hv : (4#usize).val=4 := by scalar_tac
   simp only [if_neg hp,hv]
   exact XRy_ArrayRead.mapped toClaimQ sem.before_z1 li hli

#print axioms extra
#print axioms before_z1
end XRy_ClaimSelectExtra
