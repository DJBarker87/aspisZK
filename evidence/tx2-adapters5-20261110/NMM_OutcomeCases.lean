import NMM_LaneReplies
set_option autoImplicit false
namespace NMM_OutcomeCases
open Aeneas Aeneas.Std Result AspisR1 NKP_LaneCuts

/-- Internal partition of all returning outcomes. Neither branch condition is
an admissible premise of a row root: both native branch certificates are
required before this support lemma supplies a total returning relation. -/
theorem complete {A E : Type} (actual model : core.result.Result A E)
 (errors : ∀ e, actual = .Err e → model = .Err e)
 (values : ∀ a, actual = .Ok a → model = .Ok a) : actual = model := by
 cases h : actual with
 | Err e => exact (errors e h).symm
 | Ok a => exact (values a h).symm

#print complete
#print axioms complete
end NMM_OutcomeCases
