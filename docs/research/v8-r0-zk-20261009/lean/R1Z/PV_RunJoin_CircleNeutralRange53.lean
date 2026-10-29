import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CircleNeutralRange53
open Aeneas Aeneas.Std Result

theorem next_some (r : core.ops.range.Range Usize) (h : r.start.val < r.end.val) :
    ∃ after, core.iter.range.IteratorRange.next core.iter.range.StepUsize r =
      ok (some r.start,after) ∧ after.start.val = r.start.val+1 ∧ after.end = r.end := by
  obtain ⟨⟨opt,after⟩,hr,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_Usize_some_spec r h)
  exact ⟨after,by simpa only [ho] using hr,hs,he⟩

theorem next_none (r : core.ops.range.Range Usize) (h : r.end.val ≤ r.start.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r = ok (none,r) := by
  obtain ⟨⟨opt,after⟩,hr,ho,hs⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_Usize_none_spec r h)
  simpa only [ho,hs] using hr

#print axioms next_some
#print axioms next_none
end R1Z.PV_RunJoin_CircleNeutralRange53
