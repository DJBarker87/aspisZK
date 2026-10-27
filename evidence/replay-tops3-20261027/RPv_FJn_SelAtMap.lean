import RPv_FJn_CopyMaskMap
import R0P.SemDecision
set_option autoImplicit false
namespace AspisR1.FJn_SelAtMap
variable {K L : Type} [Field K] [Field L]
/-- Tensor selector transport, including the original coordinate reversal. -/
theorem value (f : K →+* L) (p : Fin 10 → K) :
    (fun i=>f (R0P.SemSource.selAt p i))=R0P.SemSource.selAt (fun j=>f (p j)) := by
  funext i
  simp only [R0P.SemSource.selAt,R0P.SemSource.toR0,AspisR0.Opening.eqWeight,map_prod,apply_ite,map_sub,map_one]
#print axioms value
end AspisR1.FJn_SelAtMap
