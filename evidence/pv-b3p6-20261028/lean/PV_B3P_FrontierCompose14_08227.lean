import PV_B3P_FrontierCompose14_09227
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier Result
set_option autoImplicit false
theorem suffix8_binding14 (fields : FF14) :
    suffix8_14 fields = indexed14 fields [8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize, 16#usize, 17#usize, 18#usize, 19#usize] := by
  funext out values
  rw [factor8_14]
  rw [suffix9_binding14]
  rfl
#print axioms suffix8_binding14
end PV_B3P_FrontierStages14227
