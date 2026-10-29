import Aeneas.Std
namespace PV_B3P_PureBind227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem lift_bind {α β : Type} (value : α) (next : α → Result β) :
    (do let x ← lift value; next x) = (let x := value; next x) := rfl

#print axioms lift_bind
end PV_B3P_PureBind227
