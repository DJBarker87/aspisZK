import XRx_StageFold
import XRo_Join_ResultTransport
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSe_StageMap
/-- Nominal error transport through the SAME generic first-stop driver.
State, ordering, outer failures and divergence are preserved literally. -/
theorem source {S E F : Type} (error : E → F)
 (left : Nat → S → Result (core.result.Result S E))
 (right : Nat → S → Result (core.result.Result S F))
 (same : ∀ i s, mapR (inner id error) (left i s)=right i s)
 (items : List Nat) (state : core.result.Result S E) :
 mapR (inner id error) (XRx_StageFold.fold left items state)=
 XRx_StageFold.fold right items (inner id error state) := by
 induction items generalizing state with
 | nil => rfl
 | cons i rest ih =>
   cases state with
   | Err e =>
     simp only [XRx_StageFold.fold,XRx_StageFold.advance,inner,bind_tc_ok]
     exact ih (.Err e)
   | Ok s =>
     simp only [XRx_StageFold.fold,XRx_StageFold.advance,inner,mapR_bind,id_eq]
     rw [←same i s,bind_map]
     congr 1
     funext next
     exact ih next
#print axioms source
end XSe_StageMap
