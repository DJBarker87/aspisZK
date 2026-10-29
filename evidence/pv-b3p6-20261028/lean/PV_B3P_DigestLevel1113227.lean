import PV_B3P_DigestLevel11227
import PV_B3P_DigestRead917227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Success227
set_option autoImplicit false
attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root Array.index_usize
theorem digest_level_binding11_13 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_direct_stage9_17 public1 openings selectors output =
      digest_level11 public1 openings selectors output 13#usize := by
  unfold digest_direct_stage9_17 digest_read_context9_17 digest_level11
  rw [digest_shift11_13]
#print axioms digest_level_binding11_13
end PV_B3P_Binding11227
