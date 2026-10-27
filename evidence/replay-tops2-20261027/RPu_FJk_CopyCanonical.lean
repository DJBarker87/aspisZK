import RPu_JGa_Copy
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_CopyCanonical
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal
/-- Reuse total canonical source evaluation to obtain canonicality on the actual run. -/
theorem value (a : Array field.QM31 16#usize) (h1 : field.QM31) (s : Selectors)
    (lambda chi : field.QM31) (index : U64) (v : PoolV1PairForestCompiledVariantV1)
    (copy : PoolV1PairForestCompiledCopyTerminalV1)
    (ha : canonical a) (hh1 : Canon h1) (hh : canonical s.high) (hl : canonical s.low)
    (hlam : Canon lambda) (hchi : Canon chi)
    (run : evaluate_with_selectors a h1 s lambda chi index v=ok copy) :
    Canon copy.residual ∧ Canon copy.active := by
  obtain ⟨out,success,hr,hact⟩ := JGa_Copy.source a h1 s lambda chi index v ha hh1 hh hl hlam hchi
  have same : out=copy := Result.ok.inj (success.symm.trans run)
  subst out
  exact ⟨hr,hact⟩
#print axioms value
end AspisR1.FJk_CopyCanonical
end
