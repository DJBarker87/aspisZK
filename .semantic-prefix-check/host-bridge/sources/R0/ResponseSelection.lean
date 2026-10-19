import Mathlib.Tactic

/-! Choose an offending response only where one exists, for applying the
strategy-quantified agreement theorems to existential bad sets. -/
set_option autoImplicit false
namespace AspisR0.ResponseSelection
noncomputable section
variable {C R : Type*} [Inhabited R]

def selected (bad : C → R → Prop) (x : C) : R := by
  classical
  exact if h : ∃ r, bad x r then Classical.choose h else default

theorem selected_spec (bad : C → R → Prop) (x : C) (h : ∃ r, bad x r) :
    bad x (selected bad x) := by
  classical
  simpa only [selected, dif_pos h] using Classical.choose_spec h

#print axioms selected_spec
end
end AspisR0.ResponseSelection
