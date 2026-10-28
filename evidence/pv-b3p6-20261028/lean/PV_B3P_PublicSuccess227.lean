import PV_B3P_PublicCellsSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- A symbolic family satisfying the append validator: arbitrary public bytes
and roots are retained, sequence/index are0/0 ->1, both frontiers are empty. -/
def valid_public (p : reference_terminal.SemanticPublic) : reference_terminal.SemanticPublic :=
  {p with withdrawal_amount := none,
    transition := {
      live_snapshot := {p.transition.live_snapshot with pool := p.pool,
        deployment_domain := p.deployment_domain,
        sequence := 0#u64, next_pair_index := 0#u64, frontier := empty_frontier},
      candidate_afterstate := {p.transition.candidate_afterstate with
        next_pair_index := 1#u64, next_frontier := empty_frontier}}}

/-- Genuine Rust Ok of the full emitted public-transition validator. This does
not establish successful terminal/reference evaluation. -/
theorem public_transition_success (p : reference_terminal.SemanticPublic) :
    reference_terminal.validate_transition (valid_public p) = .ok (.Ok ()) := by
  have hcapacity : ¬(0#u64 >= 1048576#u64) := by scalar_tac
  have hloop := empty_transition_loop 0#u64 0#usize 20 0#usize (by rfl)
  unfold reference_terminal.validate_transition
  simp only [valid_public,bytes_ne_self,bind_tc_ok,Bool.false_eq_true,↓reduceIte,
    bne_self_eq_false,capacity_result,hcapacity,checked_next_zero,carry_zero,hloop]

#print axioms public_transition_success
end PV_B3P_Success227
