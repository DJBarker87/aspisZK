import FJn_SelectorMap
import FJn_SelAtMap
set_option autoImplicit false
namespace AspisR1.FJn_ActivePointMap
variable {K L : Type} [Field K] [Field L]
theorem value (f : K →+* L) (p : Fin 10 → K) :
    f (R0P.SemSource.activeAt p)=R0P.SemSource.activeAt (fun i=>f (p i)) := by
  unfold R0P.SemSource.activeAt
  rw [FJn_CopyMaskMap.active,FJn_SelectorMap.value,FJn_SelAtMap.value]
#print axioms value
end AspisR1.FJn_ActivePointMap
