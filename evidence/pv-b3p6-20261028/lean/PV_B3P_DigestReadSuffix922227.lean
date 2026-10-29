import PV_B3P_DigestSuffix22227
import PV_B3P_DigestRead922227
import PV_B3P_DigestReadSuffix923227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
open PV_B3P_Success227
set_option autoImplicit false

def digest_direct_suffix9_22 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q :=
  digest_direct_stage9_22 public1 openings selectors output >>= digest_direct_suffix9_23 public1 openings selectors

attribute [local irreducible] digest_direct_stage9_22 digest_direct_suffix9_23

theorem digest_suffix_read_binding9_22 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_22 public1 openings selectors output = digest_direct_suffix9_22 public1 openings selectors output := by
  rw [digest_suffix_22_equation]
  rw [digest_stage_read_binding9_22]
  change (digest_direct_stage9_22 public1 openings selectors output >>= digest_suffix_23 public1 openings selectors) = _
  apply congrArg (fun next => digest_direct_stage9_22 public1 openings selectors output >>= next)
  funext next
  exact digest_suffix_read_binding9_23 public1 openings selectors next

#print axioms digest_suffix_read_binding9_22
end PV_B3P_Binding9227
