import PV_B3P_DigestFields227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
abbrev Digest8Q := Array aspis_core.field.QM31 8#usize
def digest_stage_10 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block6 ← lift (Std.Usize.wrapping_add 34#usize 6#usize)
  let i18 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      6#u32)
  let i19 ← lift (i18 &&& 1#u64)
    if i19 = 0#u64
    then
      do
      let i20 ← lift (Std.Usize.wrapping_mul block6 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i20
      let a ← reference_terminal.empty_root 6#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i20 ← lift (Std.Usize.wrapping_mul block6 16#usize)
      let i21 ← lift (Std.Usize.wrapping_add i20 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i21
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          6#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false

theorem digest_stage_10_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_stage_10 public1 openings selectors output) := by
  unfold digest_stage_10
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

#print axioms digest_stage_10_success
end PV_B3P_Success227
