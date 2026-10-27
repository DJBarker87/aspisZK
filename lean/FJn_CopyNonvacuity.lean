import FJn_CopyFullValue
import JGa_Copy
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_CopyNonvacuity
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
/-- The complete copy VALUE hypotheses hold on actual source success for every
canonical operand. No independently assumed child output is required. -/
theorem value (a : Array field.QM31 16#usize) (h : field.QM31) (s : Selectors)
    (lambda chi : field.QM31) (index : U64) (v : PoolV1PairForestCompiledVariantV1)
    (ha : canonical a) (hh : Canon h) (hhigh : canonical s.high) (hlow : canonical s.low)
    (hlambda : Canon lambda) (hchi : Canon chi) :
    ∃ copy,evaluate_with_selectors a h s lambda chi index v=ok copy ∧
      (decode copy.residual,decode copy.active)=
        R0P.copyEvaluateWithSelectors (decoded a) (decode h) (FIw_CopyEndpoint.modelSelectors s)
          (decode lambda) (decode chi) index.val (FJk_CopyDescriptor.variant v) := by
  obtain ⟨copy,run,_,_⟩ := JGa_Copy.source a h s lambda chi index v ha hh hhigh hlow hlambda hchi
  have got := FJn_CopyFullValue.value a h s lambda chi index v copy ha hh hhigh hlow hlambda hchi run
  exact ⟨copy,run,got.2.2⟩
#print axioms value
end AspisR1.FJn_CopyNonvacuity
end
