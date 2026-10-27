import FIz_Marginals
import FIz_RangeFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_RangeMarginal
open FIv_NativeValue (K)
open FIw_PublicModel (Selectors)

theorem value (s : Selectors) (mass : (∑ l : Fin 16, FIv_NativeArray.value s.low l.val)=1)
    (start n : Nat) (bound : start+n≤64) :
    FIx_HighSumInner.model s n start 0 = R0P.g2SumHigh (FIw_PublicModel.selector s) start n bound := by
  rw [FIz_RangeFold.value]
  unfold R0P.g2SumHigh
  congr 1
  apply congrArg List.ofFn
  funext i
  exact (FIz_Marginals.high s mass ⟨start+i.val,by omega⟩).symm
#print axioms value
end AspisR1.FIz_RangeMarginal
end
