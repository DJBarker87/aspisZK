import NKE_RustBind
import NKE_EventAll
set_option autoImplicit false
namespace NKE_RustBindAll
open Aeneas Aeneas.Std Result VTop_Stages

theorem all {E A B : Type} (P : E → Prop)
 (m : NJU_Log.Run E (core.result.Result A verifier.Error))
 (k : A → NJU_Log.Run E (core.result.Result B verifier.Error))
 (hm : NKE_EventAll.Holds P m) (hk : ∀ value,NKE_EventAll.Holds P (k value)) :
 NKE_EventAll.Holds P (NKE_RustBind.bind m k) := by
 unfold NKE_RustBind.bind
 apply NKE_EventAll.bind_all P m _ hm
 intro reply
 cases reply with
 | Ok value => exact hk value
 | Err e => exact NKE_EventAll.lift_all P _
#print axioms all
end NKE_RustBindAll
