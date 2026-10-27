import FJk_CopyRowTransport
import FJk_CopyCanonical
import JGa_CopyPatterns
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_CopyRawValue
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
/-- Actual complete copy arithmetic and 136-link row, retaining only the two
remaining pattern/active model identifications as separate downstream work. -/
theorem value (a : Array field.QM31 16#usize) (h : field.QM31) (s : Selectors)
    (lambda chi : field.QM31) (index : U64) (v : PoolV1PairForestCompiledVariantV1)
    (copy : PoolV1PairForestCompiledCopyTerminalV1)
    (ha : canonical a) (hh : Canon h) (hhigh : canonical s.high) (hlow : canonical s.low)
    (hlambda : Canon lambda) (hchi : Canon chi)
    (run : evaluate_with_selectors a h s lambda chi index v=ok copy) :
    ∃ patterns : Array field.QM31 14#usize,
      pattern_values a lambda=ok patterns ∧ canonical patterns ∧
      Selectors.active s=ok copy.active ∧ Canon copy.active ∧ Canon copy.residual ∧
      decode copy.residual=decode copy.active*
        R0P.copyResidual (FJk_CopyFullFold.model s patterns index v) (decode h) (decode chi) := by
  obtain ⟨patterns,pv,pw,cv,cw,rp,rl,ra,finish⟩ := FIw_CopyEvaluation.value a h s lambda chi index v copy run
  obtain ⟨old,success,canonical⟩ := WP.spec_imp_exists (JGa_CopyPatterns.source a lambda ha hlambda)
  have same : old=patterns := Result.ok.inj (success.symm.trans rp)
  subst old
  have row := FJk_CopyFullFold.value s index v patterns pv pw cv cw hhigh hlow canonical rl
  have cc := FJk_CopyCanonical.value a h s lambda chi index v copy ha hh hhigh hlow hlambda hchi run
  have final := finish row.1 row.2.1 row.2.2.1 row.2.2.2.1 hh hchi cc.2
  refine ⟨patterns,rp,canonical,ra,cc.2,cc.1,?_⟩
  exact final.2.trans (congrArg (fun r=>decode copy.active*R0P.copyResidual r (decode h) (decode chi))
    ((FJk_CopyRowTransport.value pv pw cv cw).trans row.2.2.2.2))
#print axioms value
end AspisR1.FJk_CopyRawValue
end
