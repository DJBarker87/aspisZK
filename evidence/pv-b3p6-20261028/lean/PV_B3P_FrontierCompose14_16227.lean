import PV_B3P_FrontierCompose14_17227
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier Result
set_option autoImplicit false
theorem suffix16_binding14 (fields : FF14) :
    suffix16_14 fields = indexed14 fields [16#usize, 17#usize, 18#usize, 19#usize] := by
  funext out values
  rw [factor16_14]
  rw [suffix17_binding14]
  rfl
#print axioms suffix16_binding14
end PV_B3P_FrontierStages14227
