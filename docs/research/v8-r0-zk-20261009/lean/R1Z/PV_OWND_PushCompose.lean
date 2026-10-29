import R1Z.PV_OWND_PushSuffix
set_option autoImplicit false
namespace R1Z.PV_OWND_PushCompose
open PV_OWNC_Vector PV_OWNC_PushFold PV_OWN_View
/-- Concatenating source phases means executing the first stores then the next. -/
theorem append_eq {T : Type} (k : Codec T) (b : Buffer T) (xs ys : List T) :
 append k b (xs++ys)=append k (append k b xs) ys := by
 induction xs generalizing b with
 | nil => rfl
 | cons v vs ih => exact ih (push k b v (k.encode v))
#print axioms append_eq
end R1Z.PV_OWND_PushCompose
