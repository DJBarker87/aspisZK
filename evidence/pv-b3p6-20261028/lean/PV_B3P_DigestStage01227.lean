import PV_B3P_DigestFields227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
abbrev Digest8Q := Array aspis_core.field.QM31 8#usize
def digest_stage_01 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let i2 ← lift (Std.Usize.wrapping_mul 26#usize 16#usize)
  let i3 ← lift (Std.Usize.wrapping_add i2 11#usize)
  let q1 ← reference_copy_terminal.Selectors.row selectors i3
    reference_terminal.add_digest_binding output q1 openings.z 0#usize
      public1.nullifier false

theorem digest_stage_01_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_stage_01 public1 openings selectors output) := by
  unfold digest_stage_01
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro selector
  apply total_reference_terminal_add_digest_binding <;> scalar_tac

#print axioms digest_stage_01_success
end PV_B3P_Success227
