import PV_B3P_DigestStage00227
import PV_B3P_DigestBranch227
import PV_B3P_DigestSuffix01227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_suffix_00 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result Digest8Q := do
  let digests := Array.repeat 8#usize aspis_core.field.QM31.ZERO
  let i ← lift (Std.Usize.wrapping_mul 56#usize 16#usize)
  let i1 ← lift (Std.Usize.wrapping_add i 11#usize)
  let q ← reference_copy_terminal.Selectors.row selectors i1
  let digests1 ←
    reference_terminal.add_digest_binding digests q openings.z 0#usize
      public1.anchor false
  digest_suffix_01 public1 openings selectors digests1

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry digest_suffix_01

theorem digest_suffix_00_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    digest_suffix_00 public1 openings selectors = digest_stage_00 public1 openings selectors >>= digest_suffix_01 public1 openings selectors := by
  simp only [digest_suffix_00,digest_stage_00,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_suffix_00_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    Success (digest_suffix_00 public1 openings selectors) := by
  rw [digest_suffix_00_equation]
  apply bind
  · exact digest_stage_00_success public1 openings selectors
  intro next
  exact digest_suffix_01_success public1 openings selectors next

#print axioms digest_suffix_00_equation
#print axioms digest_suffix_00_success
end PV_B3P_Success227
