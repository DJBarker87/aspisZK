import PV_B3P_DigestFields227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_stage_03 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let i4 ← lift (Std.Usize.wrapping_mul 32#usize 16#usize)
  let i5 ← lift (Std.Usize.wrapping_add i4 11#usize)
  let q2 ← reference_copy_terminal.Selectors.row selectors i5
  reference_terminal.add_digest_binding output q2 openings.z 0#usize
    public1.change false

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry

theorem digest_stage_03_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_stage_03 public1 openings selectors output) := by
  unfold digest_stage_03
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro selector
  apply total_reference_terminal_add_digest_binding <;> scalar_tac

#print axioms digest_stage_03_success
end PV_B3P_Success227
