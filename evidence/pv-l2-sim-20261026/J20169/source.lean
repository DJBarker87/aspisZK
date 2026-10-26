import R1Z.PV_L2_Record
set_option autoImplicit false
namespace R1Z.PV_L2_RecordBind
open Aeneas Aeneas.Std Result R1Z.PV_L2_Record

theorem erase_bind {α β : Type} (run : Recorded α) (f : α → Recorded β) :
    (do let value ← run; f value).value = (do let value ← run.value; (f value).value) :=
  PV_L2_Record.bind_value run f

#print axioms erase_bind
end R1Z.PV_L2_RecordBind
