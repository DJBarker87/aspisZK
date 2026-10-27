import FJk_CopyFullFold
import JGa_CopyLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_CopyLoopNonvacuity
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIw_ArrayValue (canonical)
/-- The complete link-value hypotheses are inhabited by actual source execution
for EVERY canonical operand, rather than an assumed output-value equality. -/
theorem value (s : Selectors) (index : U64) (v : PoolV1PairForestCompiledVariantV1)
    (patterns : Array field.QM31 14#usize)
    (hh : canonical s.high) (hl : canonical s.low) (hp : canonical patterns) :
    ∃ a b c d,
      evaluate_with_selectors_loop s index v patterns
        (Array.repeat 2#usize field.QM31.ZERO) (Array.repeat 2#usize field.QM31.ZERO)
        (Array.repeat 2#usize field.QM31.ZERO) (Array.repeat 2#usize field.QM31.ZERO) 0#usize=ok (a,b,c,d) ∧
      FJk_CopyStep.row a b c d=FJk_CopyFullFold.model s patterns index v := by
  have hz := JFy_ZeroArrays.source 2#usize
  obtain ⟨a,b,c,d,run,_,_,_,_⟩ := JGa_CopyLoop.source 136 0#usize s index v patterns _ _ _ _
    rfl hh hl hp hz hz hz hz
  have got := FJk_CopyFullFold.value s index v patterns a b c d hh hl hp run
  exact ⟨a,b,c,d,run,got.2.2.2.2⟩
#print axioms value
end AspisR1.FJk_CopyLoopNonvacuity
end
