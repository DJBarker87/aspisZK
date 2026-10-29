import PV_B3P_FrontierCompose14_03227
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier Result
set_option autoImplicit false
theorem suffix2_binding14 (fields : FF14) :
    suffix2_14 fields = indexed14 fields [2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize, 16#usize, 17#usize, 18#usize, 19#usize] := by
  funext out values
  rw [factor2_14]
  rw [suffix3_binding14]
  rfl
#print axioms suffix2_binding14
end PV_B3P_FrontierStages14227
