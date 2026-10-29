import PV_B3P_DigestFields227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_stage_24 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let i46 ← lift (Std.Usize.wrapping_mul 53#usize 16#usize)
  let i47 ← lift (Std.Usize.wrapping_add i46 11#usize)
  let q3 ← reference_copy_terminal.Selectors.row selectors i47
  let digests25 ←
    reference_terminal.add_digest_binding output q3 openings.z 0#usize
      public1.transition.candidate_afterstate.next_root false
  let carry ←
    reference_terminal.bounded_append_carry
      public1.transition.live_snapshot.next_pair_index
  if carry < 20#usize
  then
    let i48 ← lift (Std.Usize.wrapping_add 33#usize carry)
    let i49 ← lift (Std.Usize.wrapping_mul i48 16#usize)
    let i50 ← lift (Std.Usize.wrapping_add i49 11#usize)
    let q4 ← reference_copy_terminal.Selectors.row selectors i50
    let a ←
      Array.index_usize public1.transition.candidate_afterstate.next_frontier
        carry
    reference_terminal.add_digest_binding digests25 q4 openings.z 0#usize a
      false
  else ok digests25

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry

theorem digest_stage_24_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_stage_24 public1 openings selectors output) := by
  unfold digest_stage_24
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro selector
  apply bind
  · apply total_reference_terminal_add_digest_binding <;> scalar_tac
  intro digests25
  apply bind
  · exact carry_total _
  intro carry
  split
  · apply lift_total
    apply lift_total
    apply lift_total
    apply bind
    · apply row_total
      apply row_address_bound
      · apply wrap_add_bound; scalar_tac
      · scalar_tac
    intro selector
    apply bind
    · apply index; scalar_tac
    intro expected
    apply total_reference_terminal_add_digest_binding <;> scalar_tac
  · exact ok _

#print axioms digest_stage_24_success
end PV_B3P_Success227
