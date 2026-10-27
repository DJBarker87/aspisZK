import RPv_FJk_CopyPatternDescriptor
set_option autoImplicit false
namespace AspisR1.FJk_PatternRegistryC
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open FJk_CopyPatternDescriptor (model)
theorem p08 : model pattern08=R0P.copyPattern8 := by
  unfold model pattern08
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p08
theorem p09 : model pattern09=R0P.copyPattern9 := by
  unfold model pattern09
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p09
theorem p10 : model pattern10=R0P.copyPattern10 := by
  unfold model pattern10
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p10
end AspisR1.FJk_PatternRegistryC
