import FJn_CopyEvaluatorMap
import FJn_CopySelectors
import FIz_ConcretePack
import FJn_SelectorMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_CopyWide
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIz_ConcretePack (embed)
/-- Same boxed selectors, with model marginals transported to Wide. -/
theorem selectors (point : Array field.QM31 10#usize) (s : FIw_PublicModel.Selectors)
    (hp : canonical point)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s) :
    FJn_CopyMaskMap.selectors embed (FIw_CopyEndpoint.modelSelectors s)=
      R0P.copySelectors (fun i=>embed (FIw_PublicModel.selector s i)) := by
  rw [FJn_CopySelectors.value point s hp run]
  exact FJn_SelectorMap.value embed (FIw_PublicModel.selector s)
/-- Complete evaluator naturality on the SAME actual native call. -/
theorem value (a : Array field.QM31 16#usize) (h : field.QM31) (s : FIw_PublicModel.Selectors)
    (lambda chi : field.QM31) (index : U64)
    (v : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
    (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1)
    (point : Array field.QM31 10#usize)
    (ha : canonical a) (hh : Canon h) (hp : canonical point)
    (hlambda : Canon lambda) (hchi : Canon chi)
    (boxed : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s)
    (run : pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h s lambda chi index v=ok copy) :
    (embed (decode copy.residual),embed (decode copy.active))=
      R0P.copyEvaluateWithSelectors (fun i=>embed (decoded a i)) (embed (decode h))
        (R0P.copySelectors (fun i=>embed (FIw_PublicModel.selector s i)))
        (embed (decode lambda)) (embed (decode chi)) index.val (FJk_CopyDescriptor.variant v) := by
  have cs:=FJa_BoxedCanonical.value point s hp boxed
  have cv:=FJn_CopyFullValue.value a h s lambda chi index v copy ha hh cs.1 cs.2 hlambda hchi run
  have mapped:=congrArg (fun (r : K×K)=>(embed r.1,embed r.2)) cv.2.2
  exact mapped.trans ((FJn_CopyEvaluatorMap.value embed (decoded a) (decode h)
    (FIw_CopyEndpoint.modelSelectors s) (decode lambda) (decode chi) index.val
    (FJk_CopyDescriptor.variant v)).trans (by rw [selectors point s hp boxed]))
#print axioms selectors
#print axioms value
end AspisR1.FJn_CopyWide
end
