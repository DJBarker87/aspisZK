import AspisR1GroupedPairActualFieldOpsV3.Funs
import Aeneas.Std.RangeIter
open Aeneas Aeneas.Std Result WP

namespace AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete

def actualGroupVal (j : Fin 64) : Nat :=
  (weights.S2_INACTIVE_GROUPS.val[j.val]'(by
    simpa [weights.S2_INACTIVE_GROUPS.property] using j.isLt)).val

theorem actual_group_table_value_bound (j : Fin 64) : actualGroupVal j < 12 := by
  fin_cases j <;> simp [actualGroupVal, weights.S2_INACTIVE_GROUPS, Array.make]

theorem generated_group_index_value_bound (j : Std.Usize) (hj : j.val < 64)
    (g : Std.U8)
    (h : Array.index_usize weights.S2_INACTIVE_GROUPS j = .ok g) : g.val < 12 := by
  have hlen : j.val < weights.S2_INACTIVE_GROUPS.length := by
    simpa [weights.S2_INACTIVE_GROUPS.property] using hj
  obtain ⟨x, hx, hvalue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec weights.S2_INACTIVE_GROUPS j hlen)
  have hxg : x = g := Result.ok.inj (hx.symm.trans h)
  have hselected : g = weights.S2_INACTIVE_GROUPS.val[j.val]'hlen := by
    calc
      g = x := hxg.symm
      _ = weights.S2_INACTIVE_GROUPS.val[j.val]'hlen := hvalue
  have hbound := actual_group_table_value_bound ⟨j.val, hj⟩
  have hv := congrArg (fun z : Std.U8 => z.val) hselected
  calc
    g.val = (weights.S2_INACTIVE_GROUPS.val[j.val]'hlen).val := by
      simpa only using hv
    _ < 12 := by
      simpa [actualGroupVal] using hbound

end AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete

#print axioms AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.actual_group_table_value_bound
#print axioms AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.generated_group_index_value_bound
