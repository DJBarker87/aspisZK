import LIBB_ObservationMap
import NMV_NoWrite
set_option autoImplicit false
namespace LIBB_NoWriteGraph
open Aeneas Aeneas.Std
open RSL NMV_NoWrite

theorem lift {A : Type} (code : Result A) : Free (NMS_R2N_Interpreted.liftResult code) := by
 cases code with
 | ok a => exact pure_free _
 | fail e => exact panic_free
 | div => intro env o h c b; subst o; exact List.not_mem_nil

theorem map {A B : Type} (f : A → B) (m : Spec A) (free : Free m) : Free (Spec.map f m) :=
 bind_free _ _ free (fun _ => pure_free _)
#print axioms lift
#print axioms map
end LIBB_NoWriteGraph
