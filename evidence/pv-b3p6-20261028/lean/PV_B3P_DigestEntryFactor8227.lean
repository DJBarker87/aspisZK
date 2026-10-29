import PV_B3P_DigestRaw8227
import PV_B3P_DigestStage00227
import PV_B3P_DigestBranch227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry

def digest_head_00 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result Digest8Q := do
  let digests := Array.repeat 8#usize aspis_core.field.QM31.ZERO
  let i ← lift (Std.Usize.wrapping_mul 56#usize 16#usize)
  let i1 ← lift (Std.Usize.wrapping_add i 11#usize)
  let q ← reference_copy_terminal.Selectors.row selectors i1
  let digests1 ←
    reference_terminal.add_digest_binding digests q openings.z 0#usize
      public1.anchor false
  digest_raw_01 public1 openings selectors digests1

theorem digest_head_00_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.public_digest_lanes public1 openings selectors = digest_head_00 public1 openings selectors := by
  unfold reference_terminal.public_digest_lanes digest_head_00 digest_raw_01
  rfl

#print axioms digest_head_00_factor
end PV_B3P_Success227
