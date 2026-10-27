import RPu_FJk_CopyPatternDescriptor
set_option autoImplicit false
namespace AspisR1.FJk_PatternRegistryA
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open FJk_CopyPatternDescriptor (model)
theorem p00 : model pattern00=R0P.copyPattern0 := by
  unfold model pattern00
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p00
theorem p01 : model pattern01=R0P.copyPattern1 := by
  unfold model pattern01
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p01
theorem p02 : model pattern02=R0P.copyPattern2 := by
  unfold model pattern02
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p02
theorem p03 : model pattern03=R0P.copyPattern3 := by
  unfold model pattern03
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p03
end AspisR1.FJk_PatternRegistryA
