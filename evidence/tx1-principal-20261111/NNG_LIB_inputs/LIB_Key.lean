import LIB_Carriers
import NFU_AdapterGetters
set_option autoImplicit false
namespace LIB_Key
open Aeneas Aeneas.Std AdapterRw
/-- CLOSED231, retaining the actual complete fixed-array key. -/
theorem result (a : r1_pool_adapter.owned.OwnedAccount) :
    r1_pool_adapter.owned.OwnedAccount.impl.key a = .ok a.key :=
  NFU_AdapterGetters.key a
#print axioms result
end LIB_Key
