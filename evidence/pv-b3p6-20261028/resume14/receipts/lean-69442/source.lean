import PV_B3P_FrontierCompose14_19227
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier Result
set_option autoImplicit false
theorem suffix18_binding14 (fields : FF14) :
    suffix18_14 fields = indexed14 fields [18#usize, 19#usize] := by
  funext out values
  rw [factor18_14]
  rw [suffix19_binding14]
  rfl
#print axioms suffix18_binding14
end PV_B3P_FrontierStages14227
