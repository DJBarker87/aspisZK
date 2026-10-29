import PV_B3P_DigestFields227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_stage_00 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result Digest8Q := do
  let digests := Array.repeat 8#usize aspis_core.field.QM31.ZERO
  let i ← lift (Std.Usize.wrapping_mul 56#usize 16#usize)
  let i1 ← lift (Std.Usize.wrapping_add i 11#usize)
  let q ← reference_copy_terminal.Selectors.row selectors i1
  reference_terminal.add_digest_binding digests q openings.z 0#usize
    public1.anchor false

theorem digest_stage_00_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    Success (digest_stage_00 public1 openings selectors) := by
  unfold digest_stage_00
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro selector
  apply total_reference_terminal_add_digest_binding <;> scalar_tac

#print axioms digest_stage_00_success
end PV_B3P_Success227
