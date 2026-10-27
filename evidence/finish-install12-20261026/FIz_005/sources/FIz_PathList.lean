import FIx_PathMeaning
import FIw_PublicModel
import R0P.Path
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_PathList
open FIv_NativeValue (K)
open FIw_PublicModel (Openings)

theorem value (q : K) (o : Openings) :
    List.ofFn (FIx_PathMeaning.coefficients q (FIv_NativeArray.value o.z 0)
      (FIv_NativeArray.value o.z) (FIv_NativeArray.value o.succ_z)) =
    R0P.pathLanes q (FIw_PublicModel.openings o) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,R0P.pathLanes,List.length_append,List.length_cons,
      List.length_nil,List.length_ofFn]
    rfl
  · intro j hj _
    have h : j<17 := hj
    rw [List.getElem_ofFn]
    by_cases h9 : 9≤j
    · simp only [FIx_PathMeaning.coefficients,if_pos h9,R0P.pathLanes,
        List.getElem_append,List.length_append,List.length_cons,List.length_nil,
        List.length_ofFn,show ¬j<1+8 by omega,↓reduceDIte,
        List.getElem_ofFn,FIw_PublicModel.openings]
      rfl
    · by_cases h1 : 1≤j
      · simp only [FIx_PathMeaning.coefficients,if_neg h9,if_pos h1,R0P.pathLanes,
          List.getElem_append,List.length_append,List.length_cons,List.length_nil,
          List.length_ofFn,show j<1+8 by omega,show ¬j<1 by omega,↓reduceDIte,
          List.getElem_ofFn,FIw_PublicModel.openings]
        rfl
      · have hj0 : j=0 := by omega
        subst j
        simp only [FIx_PathMeaning.coefficients,show ¬9≤0 by omega,show ¬1≤0 by omega,
          ↓reduceIte,R0P.pathLanes,List.getElem_append,List.length_append,
          List.length_cons,List.length_nil,List.length_ofFn,↓reduceDIte,
          List.getElem_cons_zero,FIw_PublicModel.openings]
#print axioms value
end AspisR1.FIz_PathList
end
