import NDE_LinearSteps
import RPv_FIx_HighSum
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NDE_SumComposition
open AspisR1
open FIx_HighSumInner (Selectors Range)
open FIv_NativeValue (Canon decode)

theorem source (s : Selectors) (rs : Slice Range)
    (bounds : ∀ r ∈ rs.val, r.start.val ≤ r.end.val ∧ r.end.val ≤ 64)
    (canonical : ∀ x ∈ s.high.val, Canon x) :
    ∃ out, FIq_Native.pool_v1.pair_forest_semantic_terminal.sum_high s rs = ok out ∧
      Canon out ∧ decode out = FIx_HighSumOuter.ranges rs.val s 0 := by
  exact FIx_HighSum.source s rs bounds canonical

#print axioms source
#print axioms AspisR1.FIx_HighSumInner.value
#print axioms AspisR1.FIx_HighSumOuter.value
end NDE_SumComposition
end
