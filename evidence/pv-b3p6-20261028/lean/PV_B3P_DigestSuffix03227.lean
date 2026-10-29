import PV_B3P_DigestStage03227
import PV_B3P_DigestBranch227
import PV_B3P_DigestSuffix04227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_suffix_03 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let i4 ← lift (Std.Usize.wrapping_mul 32#usize 16#usize)
  let i5 ← lift (Std.Usize.wrapping_add i4 11#usize)
  let q2 ← reference_copy_terminal.Selectors.row selectors i5
  let digests4 ←
    reference_terminal.add_digest_binding output q2 openings.z 0#usize
      public1.change false
  digest_suffix_04 public1 openings selectors digests4

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry digest_suffix_04

theorem digest_suffix_03_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_03 public1 openings selectors output = digest_stage_03 public1 openings selectors output >>= digest_suffix_04 public1 openings selectors := by
  simp only [digest_suffix_03,digest_stage_03,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_suffix_03_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_suffix_03 public1 openings selectors output) := by
  rw [digest_suffix_03_equation]
  apply bind
  · exact digest_stage_03_success public1 openings selectors output
  intro next
  exact digest_suffix_04_success public1 openings selectors next

#print axioms digest_suffix_03_equation
#print axioms digest_suffix_03_success
end PV_B3P_Success227
