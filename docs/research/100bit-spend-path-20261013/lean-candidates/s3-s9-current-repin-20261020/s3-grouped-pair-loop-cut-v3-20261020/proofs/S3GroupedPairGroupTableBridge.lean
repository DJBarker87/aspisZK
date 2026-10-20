import AspisR1GroupedPairCut.Funs
import S3S9CurrentSourceModel
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1GroupedPairCut.Proofs

/-- The emitted U8 group table and the retained source-shaped model table have
identical entries. This finite statement only unfolds the two 64-element
literal tables. -/
def actualGroupVal (j : Fin 64) : Nat :=
  (weights.S2_INACTIVE_GROUPS.val[j.val]'(by
    simpa [weights.S2_INACTIVE_GROUPS.property] using j.isLt)).val

theorem actual_group_table_eq_model (j : Fin 64) :
    actualGroupVal j = AspisR1.S3S9CurrentSourceModel.inactiveGroups.getD j.val 0 := by
  fin_cases j <;>
    simp [actualGroupVal, weights.S2_INACTIVE_GROUPS,
      AspisR1.S3S9CurrentSourceModel.inactiveGroups, Array.make]

theorem generated_group_index_eq_model (j : Std.Usize) (hj : j.val < 64)
    (g : Std.U8)
    (h : Array.index_usize weights.S2_INACTIVE_GROUPS j = .ok g) :
    g.val = AspisR1.S3S9CurrentSourceModel.inactiveGroups.getD j.val 0 := by
  have hlen : j.val < weights.S2_INACTIVE_GROUPS.length := by
    simpa [weights.S2_INACTIVE_GROUPS.property] using hj
  obtain ⟨x, hx, hvalue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec weights.S2_INACTIVE_GROUPS j hlen)
  have hxg : x = g := Result.ok.inj (hx.symm.trans h)
  have hselected : g = weights.S2_INACTIVE_GROUPS.val[j.val]'hlen := by
    calc
      g = x := hxg.symm
      _ = weights.S2_INACTIVE_GROUPS.val[j.val]'hlen := hvalue
  have hmodel := actual_group_table_eq_model ⟨j.val, hj⟩
  have hval := congrArg (fun z : Std.U8 => z.val) hselected
  simpa [actualGroupVal] using hval.trans hmodel

end AspisR1GroupedPairCut.Proofs
#print axioms AspisR1GroupedPairCut.Proofs.actual_group_table_eq_model
#print axioms AspisR1GroupedPairCut.Proofs.generated_group_index_eq_model
