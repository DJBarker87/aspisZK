import PV_B3P_RangeBinding13227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std Result
set_option autoImplicit false

theorem range_next_extraction17 (start finish : Usize) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := start, «end» := finish } =
    if start < finish then
      .ok (some start, { start := Usize.wrapping_add start 1#usize, «end» := finish })
    else .ok (none, { start := start, «end» := finish }) := by
  by_cases h : start < finish
  · have hv : start.val < finish.val := by scalar_tac
    obtain ⟨⟨item, rest⟩, execution, item_eq, start_val, end_eq⟩ :=
      WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec
        { start := start, «end» := finish } hv)
    have add_val := PV_B3P_Offset226V3.add_value start 1#usize
      (PV_B3P_Binding13227.range_increment_safe13 start finish h)
    have start_eq : rest.start = Usize.wrapping_add start 1#usize := by scalar_tac
    have rest_eq : rest = { start := Usize.wrapping_add start 1#usize, «end» := finish } := by
      cases rest
      simp_all
    simp only [h,if_true,execution,item_eq,rest_eq]
  · have hv : start.val ≥ finish.val := by scalar_tac
    obtain ⟨⟨item, rest⟩, execution, item_eq, rest_eq⟩ :=
      WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec
        { start := start, «end» := finish } hv)
    simp only [h,if_false,execution,item_eq,rest_eq]
#print axioms range_next_extraction17
end PV_B3P_Direct17227
