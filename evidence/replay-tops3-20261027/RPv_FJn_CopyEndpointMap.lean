import RPv_FJn_CopyMaskMap
import RPv_FJn_CopySmallMap
set_option autoImplicit false
namespace AspisR1.FJn_CopyEndpointMap
variable {K L : Type} [Field K] [Field L]
theorem update {I : Type} [DecidableEq I] (f : K →+* L) (a : I → K) (i : I) (x : K) :
    (fun j=>f (Function.update a i x j))=Function.update (fun j=>f (a j)) i (f x) := by
  funext j
  by_cases h : j=i
  · subst j; simp only [Function.update_self]
  · simp only [Function.update_of_ne h]
theorem row (f : K →+* L) (s : R0P.CopySelectors K) (r : Fin 1024) :
    f (R0P.copySelectorRow s r)=R0P.copySelectorRow (FJn_CopyMaskMap.selectors f s) r := by
  exact map_mul f _ _
theorem value (f : K →+* L) (a w : Fin 2 → K) (e : R0P.CopyEndpoint)
    (tag : Nat) (weight : K) (p : Fin 14 → K) (s : R0P.CopySelectors K) :
    let r:=R0P.copyAccumulateEndpoint a w e tag weight p s
    ((fun i=>f (r.1 i)),(fun i=>f (r.2 i)))=
      R0P.copyAccumulateEndpoint (fun i=>f (a i)) (fun i=>f (w i)) e tag
        (f weight) (fun i=>f (p i)) (FJn_CopyMaskMap.selectors f s) := by
  simp only [R0P.copyAccumulateEndpoint,update,map_add,map_mul,map_natCast,row]
#print axioms update
#print axioms row
#print axioms value
end AspisR1.FJn_CopyEndpointMap
