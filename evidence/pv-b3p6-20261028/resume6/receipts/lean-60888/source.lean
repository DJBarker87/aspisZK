import PV_B3P_EmptyFrontierSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- An isolated layout shift; no recurrence or field term is evaluated. -/
theorem capacity_result :
    aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY = .ok 1048576#u64 := by
  unfold aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
    aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH
  rfl

theorem checked_next_zero : reference_terminal.checked_next227 0#u64 1#u64 = .ok false := by
  unfold reference_terminal.checked_next227
  rfl

/-- The zero-bit branch terminates immediately. -/
theorem carry_zero : reference_terminal.bounded_append_carry 0#u64 = .ok 0#usize := by
  unfold reference_terminal.bounded_append_carry reference_terminal.bounded_append_carry_loop
  rw [loop.eq_1]
  have h0 : 0#usize<20#usize := by scalar_tac
  simp only [reference_terminal.bounded_append_carry_loop.body,h0,↓reduceIte,lift,bind_tc_ok]
  rfl

#print axioms capacity_result
#print axioms checked_next_zero
#print axioms carry_zero
end PV_B3P_Success227
