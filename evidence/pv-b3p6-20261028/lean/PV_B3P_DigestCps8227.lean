import PV_B3P_DigestContinue8227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry
theorem public_digest_success8 (p : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    Success (reference_terminal.public_digest_lanes p openings selectors) := by
  unfold reference_terminal.public_digest_lanes
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro selector0
  apply bind
  · apply total_reference_terminal_add_digest_binding <;> scalar_tac
  intro digests0
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro selector1
  apply bind
  · apply total_reference_terminal_add_digest_binding <;> scalar_tac
  intro digests1
  apply recipient_continue8 p.recipient digests1 openings.z selectors
  intro digests2
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro selector3
  apply bind
  · apply total_reference_terminal_add_digest_binding <;> scalar_tac
  intro digests3
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level0
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level1
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level2
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level3
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level4
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level5
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level6
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level7
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level8
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level9
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level10
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level11
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level12
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level13
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level14
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level15
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level16
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level17
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level18
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply lift_total
  apply frontier_continue8
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level19
  apply digest_ok_continue8
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro selectorlast
  apply bind
  · apply total_reference_terminal_add_digest_binding <;> scalar_tac
  intro digestslast
  apply bind
  · exact carry_total p.transition.live_snapshot.next_pair_index
  intro carry
  split
  · apply lift_total
    apply lift_total
    apply lift_total
    apply bind
    · apply row_total
      apply row_address_bound
      · apply wrap_add_bound
        scalar_tac
      · scalar_tac
    intro selector
    apply bind
    · apply index <;> scalar_tac
    intro expected
    apply total_reference_terminal_add_digest_binding <;> scalar_tac
  · exact ok _

#print axioms public_digest_success8
end PV_B3P_Success227
