import PV_B3P_PublicSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

def seed_public : reference_terminal.SemanticPublic := {
  variant := .PrivateTransfer
  pool := Array.repeat 32#usize 0#u8
  deployment_domain := Array.repeat 32#usize 0#u8
  anchor := Array.repeat 8#usize 0#u32
  nullifier := Array.repeat 8#usize 0#u32
  asset_id := 0#u32
  recipient := some (Array.repeat 8#usize 0#u32)
  change := Array.repeat 8#usize 0#u32
  withdrawal_amount := none
  transition := {
    live_snapshot := {
      pool := Array.repeat 32#usize 0#u8
      deployment_domain := Array.repeat 32#usize 0#u8
      sequence := 0#u64, next_pair_index := 0#u64
      current_root := Array.repeat 8#usize 0#u32, frontier := empty_frontier}
    candidate_afterstate := {
      next_pair_index := 1#u64, next_root := Array.repeat 8#usize 0#u32
      next_frontier := empty_frontier}}}

/-- Unconditional successful nonvacuity of the emitted validator fragment.
This is deliberately not a claim about the full reference or installed op227. -/
theorem public_nonvacuity : ∃ p : reference_terminal.SemanticPublic,
    p.withdrawal_amount=none ∧ reference_terminal.validate_transition p=.ok (.Ok ()) :=
  ⟨valid_public seed_public,rfl,public_transition_success seed_public⟩

#print axioms public_nonvacuity
end PV_B3P_Success227
