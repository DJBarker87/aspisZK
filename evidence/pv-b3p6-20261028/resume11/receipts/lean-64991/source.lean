import PV_B3P_DigestLevel1100227
import PV_B3P_DigestLevel1101227
import PV_B3P_DigestLevel1102227
import PV_B3P_DigestLevel1103227
import PV_B3P_DigestLevel1104227
import PV_B3P_DigestLevel1105227
import PV_B3P_DigestLevel1106227
import PV_B3P_DigestLevel1107227
import PV_B3P_DigestLevel1108227
import PV_B3P_DigestLevel1109227
import PV_B3P_DigestLevel1110227
import PV_B3P_DigestLevel1111227
import PV_B3P_DigestLevel1112227
import PV_B3P_DigestLevel1113227
import PV_B3P_DigestLevel1114227
import PV_B3P_DigestLevel1115227
import PV_B3P_DigestLevel1116227
import PV_B3P_DigestLevel1117227
import PV_B3P_DigestLevel1118227
import PV_B3P_DigestLevel1119227
import PV_B3P_DigestReadBridge9227
import PV_B3P_Indices2011227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Success227
set_option autoImplicit false
attribute [local irreducible] digest_level11 digest_stage_24 reference_terminal.public_digest_lanes
theorem digest_suffix_loop11 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_direct_suffix9_04 public1 openings selectors output = (do
      let next ← loop (usize_body (digest_level11 public1 openings selectors) 20#usize) (output,0#usize)
      digest_stage_24 public1 openings selectors next) := by
  rw [loop_as_fold11 (digest_level11 public1 openings selectors) 20#usize 0#usize 20 output (Eq.refl _),indices11_20]
  simp only [digest_direct_suffix9_04,digest_direct_suffix9_05,digest_direct_suffix9_06,digest_direct_suffix9_07,digest_direct_suffix9_08,digest_direct_suffix9_09,digest_direct_suffix9_10,digest_direct_suffix9_11,digest_direct_suffix9_12,digest_direct_suffix9_13,digest_direct_suffix9_14,digest_direct_suffix9_15,digest_direct_suffix9_16,digest_direct_suffix9_17,digest_direct_suffix9_18,digest_direct_suffix9_19,digest_direct_suffix9_20,digest_direct_suffix9_21,digest_direct_suffix9_22,digest_direct_suffix9_23,digest_direct_suffix9_24,digest_level_binding11_00,digest_level_binding11_01,digest_level_binding11_02,digest_level_binding11_03,digest_level_binding11_04,digest_level_binding11_05,digest_level_binding11_06,digest_level_binding11_07,digest_level_binding11_08,digest_level_binding11_09,digest_level_binding11_10,digest_level_binding11_11,digest_level_binding11_12,digest_level_binding11_13,digest_level_binding11_14,digest_level_binding11_15,digest_level_binding11_16,digest_level_binding11_17,digest_level_binding11_18,digest_level_binding11_19,PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms digest_suffix_loop11
def public_digest_source_loop11 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result Digest8Q := do
  let d0 ← digest_stage_00 public1 openings selectors
  let d1 ← digest_stage_01 public1 openings selectors d0
  let d2 ← digest_stage_02 public1 openings selectors d1
  let d3 ← digest_stage_03 public1 openings selectors d2
  let next ← loop (usize_body (digest_level11 public1 openings selectors) 20#usize) (d3,0#usize)
  digest_stage_24 public1 openings selectors next
theorem public_digest_source_loop_binding11 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.public_digest_lanes public1 openings selectors = public_digest_source_loop11 public1 openings selectors := by
  rw [public_digest_read_binding9]
  unfold digest_direct_suffix9_00 digest_direct_suffix9_01 digest_direct_suffix9_02 digest_direct_suffix9_03 public_digest_source_loop11
  apply bind_equal9
  intro d0
  apply bind_equal9
  intro d1
  apply bind_equal9
  intro d2
  apply bind_equal9
  intro d3
  exact digest_suffix_loop11 public1 openings selectors d3
#print axioms public_digest_source_loop_binding11
end PV_B3P_Binding11227
