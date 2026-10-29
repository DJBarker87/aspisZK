import R1Z.PV_RunJoin_CircleNeutralWord53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralRange53
#print core.iter.range.IteratorRange.next
#print core.iter.range.StepUsize

theorem next (s e : Usize) : core.iter.range.IteratorRange.next core.iter.range.StepUsize
    (⟨s,e⟩ : core.ops.range.Range Usize) =
    if s<e then (do
      let t ← s+1#usize
      ok (some s,(⟨t,e⟩ : core.ops.range.Range Usize)))
    else ok (none,(⟨s,e⟩ : core.ops.range.Range Usize)) := by
  rfl

#print axioms next
end R1Z.PV_RunJoin_CircleNeutralRange53
