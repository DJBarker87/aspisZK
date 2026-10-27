import RPv_FIx_PathMeaning
import RPv_FIw_PublicModel
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
    interval_cases j <;>
      simp [FIx_PathMeaning.coefficients,R0P.pathLanes,FIw_PublicModel.openings]
#print axioms value
end AspisR1.FIz_PathList
end
