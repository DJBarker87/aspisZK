import RPv_FJn_CopyMaskMap
import RPv_PathFamilyFieldTransport
set_option autoImplicit false
namespace AspisR1.FJn_SelectorMap
variable {K L : Type} [Field K] [Field L]
/-- Generic selector-marginal transport, avoiding concrete Wide reduction. -/
theorem value (f : K →+* L) (s : R0P.Sel K) :
    FJn_CopyMaskMap.selectors f (R0P.copySelectors s)=
      R0P.copySelectors (fun i=>f (s i)) := by
  have hi : (fun i=>f (R0P.g2High s i))=R0P.g2High (fun i=>f (s i)) :=
    funext (PathFamilyFieldTransport.map_high f s)
  have lo : (fun i=>f (R0P.g2Low s i))=R0P.g2Low (fun i=>f (s i)) :=
    funext (PathFamilyFieldTransport.map_low f s)
  exact congrArg₂ (fun high low=>(⟨high,low⟩ : R0P.CopySelectors L)) hi lo
#print axioms value
end AspisR1.FJn_SelectorMap
