import RPv_FIz_RangeMarginal
import RPv_FIx_PathPacked
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_PathSelector
open FIv_NativeValue (K)
open FIw_PublicModel (Selectors)
theorem value (s : Selectors)
    (hm : (∑ h : Fin 64, FIv_NativeArray.value s.high h.val)=1)
    (lm : (∑ l : Fin 16, FIv_NativeArray.value s.low l.val)=1) :
    FIx_PathPacked.selector s=R0P.pathSelector (FIw_PublicModel.selector s) := by
  unfold FIx_PathPacked.selector
  change FIx_HighSumInner.model s 6 57 0 * _ = _
  rw [FIz_RangeMarginal.value s lm 57 6 (by decide)]
  unfold R0P.pathSelector
  simp only [FIz_Marginals.low s hm]
  simp only [show (1 : Fin 16).val=1 from rfl, show (5 : Fin 16).val=5 from rfl,
    show (9 : Fin 16).val=9 from rfl, show (13 : Fin 16).val=13 from rfl]
#print axioms value
end AspisR1.FIz_PathSelector
end
