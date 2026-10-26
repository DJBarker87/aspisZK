import FIz_PathList
import FIz_PathSelector
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_PathFamily
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
theorem value (p : Public) (o : Openings) (s : Selectors)
    (hm : (∑ h : Fin 64, FIv_NativeArray.value s.high h.val)=1)
    (lm : (∑ l : Fin 16, FIv_NativeArray.value s.low l.val)=1) :
    List.ofFn (FIx_PathMeaning.coefficients (FIx_PathPacked.selector s) (FIv_NativeArray.value o.z 0)
      (FIv_NativeArray.value o.z) (FIv_NativeArray.value o.succ_z)) =
    R0P.pathFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) := by
  rw [FIz_PathList.value,FIz_PathSelector.value s hm lm]
  rfl
#print axioms value
end AspisR1.FIz_PathFamily
end
