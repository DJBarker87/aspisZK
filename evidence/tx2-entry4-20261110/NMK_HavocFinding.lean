set_option autoImplicit false
namespace NMK_HavocFinding
/-- A safety assertion over post-states is monotone under restriction of the
allowed nondeterministic transitions. Therefore a passing such assertion is
not a coverage test for every location of a havoc footprint. This says nothing
against controls which also inspect an independently checked write-event log. -/
theorem restricted_safety {S : Type} (full omitted : S → S → Prop)
 (assertion : S → S → Prop)
 (restriction : ∀ before after, omitted before after → full before after)
 (certified : ∀ before after, full before after → assertion before after) :
 ∀ before after, omitted before after → assertion before after := by
 intro before after narrowed
 exact certified before after (restriction before after narrowed)
/-- Keeping an omitted cell equal to its pre-state is precisely one such
restriction. A footprint witness needs an additional coverage/transition check;
post-state safety alone cannot detect this mutation. -/
theorem omitted_cell {S V : Type} (read : S → V) (full : S → S → Prop)
 (assertion : S → S → Prop)
 (certified : ∀ before after, full before after → assertion before after) :
 ∀ before after, (full before after ∧ read after = read before) → assertion before after := by
 exact restricted_safety full (fun before after => full before after ∧ read after = read before)
  assertion (fun _ _ h => h.1) certified
#print restricted_safety
#print omitted_cell
#print axioms restricted_safety
#print axioms omitted_cell
end NMK_HavocFinding
