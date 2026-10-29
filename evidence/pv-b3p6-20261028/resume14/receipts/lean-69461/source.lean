import PV_B3P_FrontierCompose14_00227
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier
set_option autoImplicit false
/-- Exact extracted caller, preserving every Result and partial Err output,
composed through twenty named stage laws. No fields or Vec law is assumed. -/
theorem frontier_indexed_binding14 (fields : FF14) :
    frontier fields = indexed14 fields [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize, 16#usize, 17#usize, 18#usize, 19#usize] :=
  Eq.trans (raw_frontier_binding14 fields) (suffix0_binding14 fields)
#print axioms frontier_indexed_binding14
end PV_B3P_FrontierStages14227
