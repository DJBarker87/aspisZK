import RPv_FJn_FoldMap
import R0P.SemDecision
set_option autoImplicit false
namespace AspisR1.FJn_EqualityMap
variable {K L : Type} [Field K] [Field L]
/-- Transport of all ten equality factors without evaluating field elements. -/
theorem value (f : K →+* L) (a b : Fin 10 → K) :
    f (R0P.SemSource.eqValue a b)=R0P.SemSource.eqValue (fun i=>f (a i)) (fun i=>f (b i)) := by
  simp only [R0P.SemSource.eqValue,map_prod,map_add,map_sub,map_one,map_mul]
#print axioms value
end AspisR1.FJn_EqualityMap
