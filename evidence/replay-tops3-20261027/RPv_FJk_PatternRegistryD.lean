import RPv_FJk_CopyPatternDescriptor
set_option autoImplicit false
namespace AspisR1.FJk_PatternRegistryD
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open FJk_CopyPatternDescriptor (model)
theorem p11 : model pattern11=R0P.copyPattern11 := by
  unfold model pattern11
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p11
theorem p12 : model pattern12=R0P.copyPattern12 := by
  unfold model pattern12
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p12
theorem p13 : model pattern13=R0P.copyPattern13 := by
  unfold model pattern13
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p13
end AspisR1.FJk_PatternRegistryD
