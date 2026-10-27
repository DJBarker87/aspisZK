import RPu_FJk_PatternRegistryA
import RPu_FJk_PatternRegistryB
import RPu_FJk_PatternRegistryC
import RPu_FJk_PatternRegistryD
set_option autoImplicit false
namespace AspisR1.FJk_PatternRegistry
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open FJh_Base (cell)
open FJk_CopyPatternDescriptor (model)
/-- Every literal native pattern descriptor has the corresponding model meaning. -/
theorem value (i : Fin 14) : model (cell constants.COPY_PATTERNS i)=R0P.copyPatterns i := by
  unfold constants.COPY_PATTERNS
  fin_cases i
  all_goals first
    | exact FJk_PatternRegistryA.p00 | exact FJk_PatternRegistryA.p01
    | exact FJk_PatternRegistryA.p02 | exact FJk_PatternRegistryA.p03
    | exact FJk_PatternRegistryB.p04 | exact FJk_PatternRegistryB.p05
    | exact FJk_PatternRegistryB.p06 | exact FJk_PatternRegistryB.p07
    | exact FJk_PatternRegistryC.p08 | exact FJk_PatternRegistryC.p09
    | exact FJk_PatternRegistryC.p10 | exact FJk_PatternRegistryD.p11
    | exact FJk_PatternRegistryD.p12 | exact FJk_PatternRegistryD.p13
#print axioms value
end AspisR1.FJk_PatternRegistry
