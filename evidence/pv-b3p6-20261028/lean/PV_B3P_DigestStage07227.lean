import PV_B3P_DigestFields227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_stage_07 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block3 ← lift (Std.Usize.wrapping_add 34#usize 3#usize)
  let i12 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      3#u32)
  let i13 ← lift (i12 &&& 1#u64)
  if i13 = 0#u64
  then
    do
    let i14 ← lift (Std.Usize.wrapping_mul block3 16#usize)
    let q3 ← reference_copy_terminal.Selectors.row selectors i14
    let a ← reference_terminal.empty_root 3#usize
    reference_terminal.add_digest_binding output q3 openings.z
      aspis_statement.poseidon2.RATE a true
  else
    do
    let i14 ← lift (Std.Usize.wrapping_mul block3 16#usize)
    let i15 ← lift (Std.Usize.wrapping_add i14 12#usize)
    let q3 ← reference_copy_terminal.Selectors.row selectors i15
    let a ←
      reference_terminal.digest227 public1.transition.live_snapshot.frontier
        3#usize
    reference_terminal.add_digest_binding output q3 openings.z 0#usize a
      false

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry

theorem digest_stage_07_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_stage_07 public1 openings selectors output) := by
  unfold digest_stage_07
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

#print axioms digest_stage_07_success
end PV_B3P_Success227
