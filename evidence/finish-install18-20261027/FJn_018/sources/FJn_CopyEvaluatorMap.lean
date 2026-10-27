import FJn_CopyRowMap
import FJn_CopyPatternMap
set_option autoImplicit false
namespace AspisR1.FJn_CopyEvaluatorMap
variable {K L : Type} [Field K] [Field L]
attribute [local irreducible] R0P.copyLinks R0P.copyResidual R0P.copyActiveLiteral
  R0P.copyPatternValuesLiteral
theorem value (f : K →+* L) (o : Fin 16 → K) (h : K) (s : R0P.CopySelectors K)
    (lambda chi : K) (n : Nat) (v : R0P.Variant) :
    let r:=R0P.copyEvaluateWithSelectors o h s lambda chi n v
    (f r.1,f r.2)=R0P.copyEvaluateWithSelectors (fun i=>f (o i)) (f h)
      (FJn_CopyMaskMap.selectors f s) (f lambda) (f chi) n v := by
  unfold R0P.copyEvaluateWithSelectors
  change (f (R0P.copyActiveLiteral s * R0P.copyResidual
    (R0P.copyLinks.foldl (FJn_CopyRowMap.stepFn s (R0P.copyPatternValuesLiteral o lambda) n v)
      ⟨fun _=>0,fun _=>0,fun _=>0,fun _=>0⟩) h chi),f (R0P.copyActiveLiteral s))=_
  rw [map_mul,FJn_CopyRowMap.residual,FJn_CopyMaskMap.active]
  rw [FJn_FoldMap.value (FJn_CopyRowMap.row f) _ _ _
    (FJn_CopyRowMap.step f s (R0P.copyPatternValuesLiteral o lambda) n v)]
  rw [FJn_CopyPatternMap.value]
  simp only [FJn_CopyRowMap.row,map_zero]
  rfl
#print axioms value
end AspisR1.FJn_CopyEvaluatorMap
