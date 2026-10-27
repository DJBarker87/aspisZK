import RPu_FIz_RangeMarginal
import RPu_FIx_ScheduleModel
import R0P.Schedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ScheduleNodes
open FIv_NativeValue (K)
open FIw_PublicModel (Selectors)
theorem value (s : Selectors)
    (lm : (∑ l : Fin 16, FIv_NativeArray.value s.low l.val)=1) :
    FIx_ScheduleModel.nodes s=R0P.scheduleNodes (FIw_PublicModel.selector s) := by
  unfold FIx_ScheduleModel.nodes FIx_HighSumOuter.ranges FIx_ScheduleModel.nodeRanges
  change FIx_HighSumInner.model s 24 33 (FIx_HighSumInner.model s 21 4 0)=_
  rw [FIz_RangeFold.value,FIz_RangeFold.value]
  unfold R0P.scheduleNodes
  rw [List.foldl_append]
  have a : (List.ofFn (fun i : Fin 24 => FIv_NativeArray.value s.high (33+i.val))) =
      List.ofFn (fun i : Fin 24 => R0P.g2High (FIw_PublicModel.selector s) ⟨33+i.val,by omega⟩) := by
    apply congrArg List.ofFn
    funext i
    exact (FIz_Marginals.high s lm ⟨33+i.val,by omega⟩).symm
  have b : (List.ofFn (fun i : Fin 21 => FIv_NativeArray.value s.high (4+i.val))) =
      List.ofFn (fun i : Fin 21 => R0P.g2High (FIw_PublicModel.selector s) ⟨4+i.val,by omega⟩) := by
    apply congrArg List.ofFn
    funext i
    exact (FIz_Marginals.high s lm ⟨4+i.val,by omega⟩).symm
  rw [a,b]
#print axioms value
end AspisR1.FIz_ScheduleNodes
end
