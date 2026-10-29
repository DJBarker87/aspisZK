import PV_B3P_DigestSuffix17227
import PV_B3P_DigestRead917227
import PV_B3P_DigestReadSuffix918227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
open PV_B3P_Success227
set_option autoImplicit false

def digest_direct_suffix9_17 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q :=
  digest_direct_stage9_17 public1 openings selectors output >>= digest_direct_suffix9_18 public1 openings selectors

attribute [local irreducible] digest_direct_stage9_17 digest_direct_suffix9_18

theorem digest_suffix_read_binding9_17 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_17 public1 openings selectors output = digest_direct_suffix9_17 public1 openings selectors output := by
  rw [digest_suffix_17_equation]
  rw [digest_stage_read_binding9_17]
  change (digest_direct_stage9_17 public1 openings selectors output >>= digest_suffix_18 public1 openings selectors) = _
  apply congrArg (fun next => digest_direct_stage9_17 public1 openings selectors output >>= next)
  funext next
  exact digest_suffix_read_binding9_18 public1 openings selectors next

#print axioms digest_suffix_read_binding9_17
end PV_B3P_Binding9227
