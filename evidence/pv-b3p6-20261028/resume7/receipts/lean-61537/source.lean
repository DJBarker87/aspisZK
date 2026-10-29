import PV_B3P_Success227
import PV_B3P_E227_17
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

def EndpointSafe (p : reference_copy_terminal.CompiledPoolV1PairForestEndpoint) : Prop :=
  p.row.val<1024 ∧ p.slot.val<2 ∧ p.pattern.val<14

def LinkSafe (l : reference_copy_terminal.CompiledPoolV1PairForestLink) : Prop :=
  l.weight_kind.val≤4 ∧ EndpointSafe l.producer ∧ EndpointSafe l.consumer

/-- Only the finite constant-data fields are inspected here. No field
arithmetic, terminal recurrence or reference execution is normalized. -/
theorem links_safe (l : reference_copy_terminal.CompiledPoolV1PairForestLink)
    (hl : l ∈ reference_copy_terminal.constants.COPY_LINKS.val) : LinkSafe l := by
  unfold reference_copy_terminal.constants.COPY_LINKS at hl
  simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨by scalar_tac,⟨by scalar_tac,by scalar_tac,by scalar_tac⟩,⟨by scalar_tac,by scalar_tac,by scalar_tac⟩⟩

#print axioms links_safe
end PV_B3P_Success227
