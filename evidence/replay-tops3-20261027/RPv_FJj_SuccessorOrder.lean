import RPv_FJj_SuccessorModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorOrder

theorem order : ((List.range 10).map FJj_SuccessorModel.index)=(List.finRange 10) := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_finRange]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_finRange]
    apply Fin.ext
    exact Nat.mod_eq_of_lt (by simpa only [List.length_map,List.length_range] using hi)

theorem value {K : Type} [Field K] (z : Fin 10 → K) :
    (FJj_SuccessorModel.eval z 10 (1,z)).2=FJd_LoopReference.successor z := by
  unfold FJj_SuccessorModel.eval FJd_LoopReference.successor
  rw [←order,←List.map_reverse,List.foldl_map]
#print axioms order
#print axioms value
end AspisR1.FJj_SuccessorOrder
end
