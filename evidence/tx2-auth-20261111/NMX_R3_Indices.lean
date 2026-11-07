import Aeneas
set_option autoImplicit false
namespace NMX_R3_Indices
open Aeneas Aeneas.Std
theorem v0 : (0#usize).val = 0 := by scalar_tac
theorem v4 : (4#usize).val = 4 := by scalar_tac
theorem v5 : (5#usize).val = 5 := by scalar_tac
theorem v6 : (6#usize).val = 6 := by scalar_tac
theorem v7 : (7#usize).val = 7 := by scalar_tac
theorem v8 : (8#usize).val = 8 := by scalar_tac
theorem v16 : (16#usize).val = 16 := by scalar_tac
theorem v20 : (20#usize).val = 20 := by scalar_tac
theorem v32 : (32#usize).val = 32 := by scalar_tac
theorem v40 : (40#usize).val = 40 := by scalar_tac
theorem v72 : (72#usize).val = 72 := by scalar_tac
theorem v73 : (73#usize).val = 73 := by scalar_tac
theorem v80 : (80#usize).val = 80 := by scalar_tac
theorem v768 : (768#usize).val = 768 := by scalar_tac
#print axioms v0
#print axioms v4
#print axioms v5
#print axioms v6
#print axioms v7
#print axioms v8
#print axioms v16
#print axioms v20
#print axioms v32
#print axioms v40
#print axioms v72
#print axioms v73
#print axioms v80
#print axioms v768
end NMX_R3_Indices
