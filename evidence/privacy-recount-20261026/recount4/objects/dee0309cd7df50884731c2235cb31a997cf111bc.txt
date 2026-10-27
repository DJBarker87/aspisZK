import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_Merkle
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_RawSelectedMismatch
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- A selected source equation places no restriction on the supplied raw entry.
This is an interface countermodel, not a counterexample to shipped Rust. -/
theorem raw_entry_unconstrained (ops : ExternalFuns) :
    ∃ other : ExternalFuns,
      other.op82 = .fail .panic ∧
      (PV_CB_Merkle.selected other).op82 = .ok 113#u8 ∧
      (ProverRwP6BodyStore.selected other).op82 = .ok 113#u8 := by
  exact ⟨{ops with op82 := .fail .panic}, rfl, rfl, rfl⟩
/-- Thus the arbitrary raw entry cannot be discharged by a selected-record law. -/
theorem no_universal_raw_source (ops : ExternalFuns) :
    ¬ (∀ other : ExternalFuns, other.op82 = .ok 113#u8) := by
  intro h
  have bad := h {ops with op82 := .fail .panic}
  cases bad
#print axioms raw_entry_unconstrained
#print axioms no_universal_raw_source
#print axioms ProverRwP6BodyData.refinement_of_data
end R1Z.PV_Join_RawSelectedMismatch
