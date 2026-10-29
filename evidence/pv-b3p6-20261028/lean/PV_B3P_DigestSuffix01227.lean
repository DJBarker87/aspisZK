import PV_B3P_DigestStage01227
import PV_B3P_DigestAssoc227
import PV_B3P_DigestSuffix02227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_suffix_01 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let i2 ← lift (Std.Usize.wrapping_mul 26#usize 16#usize)
  let i3 ← lift (Std.Usize.wrapping_add i2 11#usize)
  let q1 ← reference_copy_terminal.Selectors.row selectors i3
  let digests2 ←
    reference_terminal.add_digest_binding output q1 openings.z 0#usize
      public1.nullifier false
  digest_suffix_02 public1 openings selectors digests2

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry digest_suffix_02

theorem digest_suffix_01_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_01 public1 openings selectors output = digest_stage_01 public1 openings selectors output >>= digest_suffix_02 public1 openings selectors := by
  simp only [digest_suffix_01,digest_stage_01,digest_assoc]

theorem digest_suffix_01_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_suffix_01 public1 openings selectors output) := by
  rw [digest_suffix_01_equation]
  apply bind
  · exact digest_stage_01_success public1 openings selectors output
  intro next
  exact digest_suffix_02_success public1 openings selectors next

#print axioms digest_suffix_01_equation
#print axioms digest_suffix_01_success
end PV_B3P_Success227
