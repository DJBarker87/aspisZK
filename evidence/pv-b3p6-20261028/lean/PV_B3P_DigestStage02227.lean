import PV_B3P_DigestFields227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
abbrev Digest8Q := Array aspis_core.field.QM31 8#usize
def digest_stage_02 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
    match public1.recipient with
    | none => ok output
    | some recipient =>
      do
      let i4 ← lift (Std.Usize.wrapping_mul 29#usize 16#usize)
      let i5 ← lift (Std.Usize.wrapping_add i4 11#usize)
      let q2 ← reference_copy_terminal.Selectors.row selectors i5
      reference_terminal.add_digest_binding output q2 openings.z 0#usize
        recipient false

theorem digest_stage_02_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_stage_02 public1 openings selectors output) := by
  unfold digest_stage_02
  cases public1.recipient with
  | none => exact ok _
  | some expected =>
    apply lift_total
    apply lift_total
    apply bind
    · apply row_total
      apply row_address_bound <;> scalar_tac
    intro selector
    apply total_reference_terminal_add_digest_binding <;> scalar_tac

#print axioms digest_stage_02_success
end PV_B3P_Success227
