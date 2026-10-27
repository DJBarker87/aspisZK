import FIz_RangeMarginal
import FIx_PathPacked
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
#print axioms value
end AspisR1.FIz_PathSelector
end
