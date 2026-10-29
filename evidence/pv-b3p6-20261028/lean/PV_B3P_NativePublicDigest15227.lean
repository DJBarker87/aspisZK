import PV_B3P_DigestLoopBridge11227
import PV_B3P_RangeFold13227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def native_public_digest15 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result Digest8Q := do
  let d0 ← digest_stage_00 public1 openings selectors
  let d1 ← digest_stage_01 public1 openings selectors d0
  let d2 ← digest_stage_02 public1 openings selectors d1
  let d3 ← digest_stage_03 public1 openings selectors d2
  let next ← range_loop13 (digest_level11 public1 openings selectors) 0#usize 20#usize d3
  digest_stage_24 public1 openings selectors next

theorem native_public_digest_binding15 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    native_public_digest15 public1 openings selectors = reference_terminal.public_digest_lanes public1 openings selectors := by
  rw [public_digest_source_loop_binding11]
  unfold native_public_digest15 public_digest_source_loop11
  simp only [range_loop_binding13]
#print axioms native_public_digest_binding15
end PV_B3P_Native15227
