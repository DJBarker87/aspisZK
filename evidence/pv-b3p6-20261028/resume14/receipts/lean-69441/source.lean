import PV_B3P_FrontierIndexedBase14227
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier Result
set_option autoImplicit false
theorem suffix19_binding14 (fields : FF14) :
    suffix19_14 fields = indexed14 fields [19#usize] := by
  funext out values
  rw [factor19_14]
  rw [suffix20_binding14]
  rfl
#print axioms suffix19_binding14
end PV_B3P_FrontierStages14227
