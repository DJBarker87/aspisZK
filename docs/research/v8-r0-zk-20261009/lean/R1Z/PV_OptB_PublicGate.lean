import R1Z.PV_OptB_ChallengeDifference
set_option autoImplicit false
namespace R1Z.PV_OptB_PublicGate

/-- Exact remaining public-gate issue: opposite witness predicates yield
opposite full acceptance only when the common public gate is true. -/
theorem accepted_opposite (publicGate left right : Prop) (different : left ↔ ¬ right)
    (passes : publicGate) : (publicGate ∧ left) ↔ ¬ (publicGate ∧ right) := by
  tauto

/-- A shared false gate masks every private verdict, illustrating why the
pole-pair construction alone cannot establish a reached failure difference. -/
theorem rejected_together (publicGate left right : Prop) (fails : ¬ publicGate) :
    ¬ (publicGate ∧ left) ∧ ¬ (publicGate ∧ right) := by
  exact ⟨fun h => fails h.1,fun h => fails h.1⟩

#print axioms accepted_opposite
#print axioms rejected_together
end R1Z.PV_OptB_PublicGate
