import AspisR1GroupedPairCut.Proofs.S3GroupedPairArrayMeaning
import AspisR1GroupedPairActualFieldOpsV3.Funs

namespace S3ActualGroupTableTransfer

theorem actual_table_eq_old :
    AspisR1GroupedPairActualFieldOpsV3.weights.S2_INACTIVE_GROUPS =
      AspisR1GroupedPairCut.weights.S2_INACTIVE_GROUPS := by
  unfold AspisR1GroupedPairActualFieldOpsV3.weights.S2_INACTIVE_GROUPS
    AspisR1GroupedPairCut.weights.S2_INACTIVE_GROUPS
  rfl

theorem actual_group_index_value_bound
    (j : Aeneas.Std.Usize) (hj : j.val < 64)
    (g : Aeneas.Std.U8)
    (h : Aeneas.Std.Array.index_usize
      AspisR1GroupedPairActualFieldOpsV3.weights.S2_INACTIVE_GROUPS j = .ok g) :
    g.val < 12 := by
  rw [actual_table_eq_old] at h
  exact AspisR1GroupedPairCut.Proofs.grouped_pair_group_table_bound j hj g h

end S3ActualGroupTableTransfer

#print axioms S3ActualGroupTableTransfer.actual_table_eq_old
#print axioms S3ActualGroupTableTransfer.actual_group_index_value_bound
