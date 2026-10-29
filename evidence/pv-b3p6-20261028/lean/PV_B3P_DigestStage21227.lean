import PV_B3P_DigestFields227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_stage_21 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block17 ← lift (Std.Usize.wrapping_add 34#usize 17#usize)
  let i40 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      17#u32)
  let i41 ← lift (i40 &&& 1#u64)
  if i41 = 0#u64
  then
    do
    let i42 ← lift (Std.Usize.wrapping_mul block17 16#usize)
    let q3 ← reference_copy_terminal.Selectors.row selectors i42
    let a ← reference_terminal.empty_root 17#usize
    reference_terminal.add_digest_binding output q3 openings.z
      aspis_statement.poseidon2.RATE a true
  else
    do
    let i42 ← lift (Std.Usize.wrapping_mul block17 16#usize)
    let i43 ← lift (Std.Usize.wrapping_add i42 12#usize)
    let q3 ← reference_copy_terminal.Selectors.row selectors i43
    let a ←
      reference_terminal.digest227 public1.transition.live_snapshot.frontier
        17#usize
    reference_terminal.add_digest_binding output q3 openings.z 0#usize a
      false

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry

theorem digest_stage_21_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_stage_21 public1 openings selectors output) := by
  unfold digest_stage_21
  apply lift_total
  apply lift_total
  apply lift_total
  split
  · apply lift_total
    apply bind
    · apply row_total
      apply row_mul_bound
      apply wrap_add_bound; scalar_tac
    intro selector
    apply bind
    · apply empty_root_total; scalar_tac
    intro expected
    apply total_reference_terminal_add_digest_binding
    unfold aspis_statement.poseidon2.RATE
    scalar_tac
  · apply lift_total
    apply lift_total
    apply bind
    · apply row_total
      apply row_address_bound
      · apply wrap_add_bound; scalar_tac
      · scalar_tac
    intro selector
    apply bind
    · apply digest_total; scalar_tac
    intro expected
    apply total_reference_terminal_add_digest_binding <;> scalar_tac

#print axioms digest_stage_21_success
end PV_B3P_Success227
