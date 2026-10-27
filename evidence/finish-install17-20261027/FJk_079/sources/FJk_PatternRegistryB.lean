import FJk_CopyPatternDescriptor
set_option autoImplicit false
namespace AspisR1.FJk_PatternRegistryB
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open FJk_CopyPatternDescriptor (model)
theorem p04 : model pattern04=R0P.copyPattern4 := by
  unfold model pattern04
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p04
theorem p05 : model pattern05=R0P.copyPattern5 := by
  unfold model pattern05
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p05
theorem p06 : model pattern06=R0P.copyPattern6 := by
  unfold model pattern06
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p06
theorem p07 : model pattern07=R0P.copyPattern7 := by
  unfold model pattern07
  congr 1 <;> funext j <;> fin_cases j <;> rfl
#print axioms p07
end AspisR1.FJk_PatternRegistryB
