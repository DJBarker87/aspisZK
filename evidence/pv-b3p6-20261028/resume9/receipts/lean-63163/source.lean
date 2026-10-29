import PV_B3P_DigestSuffix00227
import PV_B3P_DigestReadSuffix901227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
open PV_B3P_Success227
set_option autoImplicit false

def digest_direct_suffix9_00 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result Digest8Q :=
  digest_stage_00 public1 openings selectors >>= digest_direct_suffix9_01 public1 openings selectors

attribute [local irreducible] digest_stage_00 digest_direct_suffix9_01

theorem digest_suffix_read_binding9_00 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    digest_suffix_00 public1 openings selectors = digest_direct_suffix9_00 public1 openings selectors := by
  rw [digest_suffix_00_equation]
  change (digest_stage_00 public1 openings selectors >>= digest_suffix_01 public1 openings selectors) = _
  apply congrArg (fun next => digest_stage_00 public1 openings selectors >>= next)
  funext next
  exact digest_suffix_read_binding9_01 public1 openings selectors next

#print axioms digest_suffix_read_binding9_00
end PV_B3P_Binding9227
