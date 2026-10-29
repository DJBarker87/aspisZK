import PV_B3P_DigestSuffix00227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
theorem digest_factor8 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.public_digest_lanes public1 openings selectors =
      digest_suffix_00 public1 openings selectors := by
  rfl
#print axioms digest_factor8
theorem public_digest_success8 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    Success (reference_terminal.public_digest_lanes public1 openings selectors) := by
  rw [digest_factor8]
  exact digest_suffix_00_success public1 openings selectors
#print axioms public_digest_success8
end PV_B3P_Success227
