import PV_B3P_FrontierCompose14_14227
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier Result
set_option autoImplicit false
theorem suffix13_binding14 (fields : FF14) :
    suffix13_14 fields = indexed14 fields [13#usize, 14#usize, 15#usize, 16#usize, 17#usize, 18#usize, 19#usize] := by
  funext out values
  rw [factor13_14]
  rw [suffix14_binding14]
  rfl
#print axioms suffix13_binding14
end PV_B3P_FrontierStages14227
