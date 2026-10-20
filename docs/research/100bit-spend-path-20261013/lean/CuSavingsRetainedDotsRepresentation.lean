import CuSavingsRetainedDotsBinding
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedDotsRepresentation
open Aeneas Aeneas.Std Result CuSavingsRetainedDotsBinding
open CuSavingsCanonicalDotsPush

theorem new_recover (state : D.New) : toNew (fromNew state)=state := rfl

theorem old_recover (state : D.Old) (hc : RelatedCounts state) :
    toOld (fromOld state)=state := by
  rcases state with ⟨⟨left,lc⟩,⟨right,rc⟩,count⟩
  rcases hc with ⟨hl,hr⟩
  change lc=count at hl
  change rc=count at hr
  cases hl
  cases hr
  rfl

theorem old_initial_recover :
    toOld (fromOld CuSavingsCanonicalDotsInvariant.initial)=CuSavingsCanonicalDotsInvariant.initial :=
  rfl

variable [AspisR1CanonicalDots.Shared]
/-- Every successful original push preserves exact recoverability of the
private state, before the source caller's next push. Rejected pushes are
immediately unwrapped to panic by the actual tail client. -/
theorem old_success_recover (state after : D.Old) (value : D.E) (scalar : D.K)
    (hc : RelatedCounts state) (hv : CuSavingsCanonicalDotsField.WideCanonical value)
    (h : AspisR1CanonicalDots.old_pairing.EbyKDot.push state value scalar=.ok (.Ok (),after)) :
    toOld (fromOld after)=after :=
  old_recover after (CuSavingsCanonicalDotsInvariant.push_counts state after value scalar hv hc h)

#print axioms new_recover
#print axioms old_recover
#print axioms old_initial_recover
#print axioms old_success_recover
end AspisR1.CuSavingsRetainedDotsRepresentation
