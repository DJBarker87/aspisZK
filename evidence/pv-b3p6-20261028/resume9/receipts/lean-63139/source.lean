import PV_B3P_DigestSuffix24227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
open PV_B3P_Success227
set_option autoImplicit false

def digest_direct_suffix9_24 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q :=
  digest_stage_24 public1 openings selectors output

attribute [local irreducible] digest_stage_24

theorem digest_suffix_read_binding9_24 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_24 public1 openings selectors output = digest_direct_suffix9_24 public1 openings selectors output := by
  rw [digest_suffix_24_equation]
  rfl

#print axioms digest_suffix_read_binding9_24
end PV_B3P_Binding9227
