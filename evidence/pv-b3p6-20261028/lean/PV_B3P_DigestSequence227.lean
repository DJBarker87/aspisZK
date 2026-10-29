import PV_B3P_DigestStage00227
import PV_B3P_DigestStage01227
import PV_B3P_DigestStage02227
import PV_B3P_DigestStage03227
import PV_B3P_DigestStage04227
import PV_B3P_DigestStage05227
import PV_B3P_DigestStage06227
import PV_B3P_DigestStage07227
import PV_B3P_DigestStage08227
import PV_B3P_DigestStage09227
import PV_B3P_DigestStage10227
import PV_B3P_DigestStage11227
import PV_B3P_DigestStage12227
import PV_B3P_DigestStage13227
import PV_B3P_DigestStage14227
import PV_B3P_DigestStage15227
import PV_B3P_DigestStage16227
import PV_B3P_DigestStage17227
import PV_B3P_DigestStage18227
import PV_B3P_DigestStage19227
import PV_B3P_DigestStage20227
import PV_B3P_DigestStage21227
import PV_B3P_DigestStage22227
import PV_B3P_DigestStage23227
import PV_B3P_DigestStage24227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_sequence (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result Digest8Q := do
  let d0 ← digest_stage_00 public1 openings selectors
  let d1 ← digest_stage_01 public1 openings selectors d0
  let d2 ← digest_stage_02 public1 openings selectors d1
  let d3 ← digest_stage_03 public1 openings selectors d2
  let d4 ← digest_stage_04 public1 openings selectors d3
  let d5 ← digest_stage_05 public1 openings selectors d4
  let d6 ← digest_stage_06 public1 openings selectors d5
  let d7 ← digest_stage_07 public1 openings selectors d6
  let d8 ← digest_stage_08 public1 openings selectors d7
  let d9 ← digest_stage_09 public1 openings selectors d8
  let d10 ← digest_stage_10 public1 openings selectors d9
  let d11 ← digest_stage_11 public1 openings selectors d10
  let d12 ← digest_stage_12 public1 openings selectors d11
  let d13 ← digest_stage_13 public1 openings selectors d12
  let d14 ← digest_stage_14 public1 openings selectors d13
  let d15 ← digest_stage_15 public1 openings selectors d14
  let d16 ← digest_stage_16 public1 openings selectors d15
  let d17 ← digest_stage_17 public1 openings selectors d16
  let d18 ← digest_stage_18 public1 openings selectors d17
  let d19 ← digest_stage_19 public1 openings selectors d18
  let d20 ← digest_stage_20 public1 openings selectors d19
  let d21 ← digest_stage_21 public1 openings selectors d20
  let d22 ← digest_stage_22 public1 openings selectors d21
  let d23 ← digest_stage_23 public1 openings selectors d22
  digest_stage_24 public1 openings selectors d23

attribute [local irreducible] digest_stage_00 digest_stage_01 digest_stage_02 digest_stage_03 digest_stage_04 digest_stage_05 digest_stage_06 digest_stage_07 digest_stage_08 digest_stage_09 digest_stage_10 digest_stage_11 digest_stage_12 digest_stage_13 digest_stage_14 digest_stage_15 digest_stage_16 digest_stage_17 digest_stage_18 digest_stage_19 digest_stage_20 digest_stage_21 digest_stage_22 digest_stage_23 digest_stage_24
theorem digest_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.public_digest_lanes public1 openings selectors =
      digest_sequence public1 openings selectors := by
  rfl
#print axioms digest_factor
theorem digest_sequence_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    Success (digest_sequence public1 openings selectors) := by
  unfold digest_sequence
  apply bind
  · exact digest_stage_00_success public1 openings selectors
  intro d0
  apply bind
  · exact digest_stage_01_success public1 openings selectors d0
  intro d1
  apply bind
  · exact digest_stage_02_success public1 openings selectors d1
  intro d2
  apply bind
  · exact digest_stage_03_success public1 openings selectors d2
  intro d3
  apply bind
  · exact digest_stage_04_success public1 openings selectors d3
  intro d4
  apply bind
  · exact digest_stage_05_success public1 openings selectors d4
  intro d5
  apply bind
  · exact digest_stage_06_success public1 openings selectors d5
  intro d6
  apply bind
  · exact digest_stage_07_success public1 openings selectors d6
  intro d7
  apply bind
  · exact digest_stage_08_success public1 openings selectors d7
  intro d8
  apply bind
  · exact digest_stage_09_success public1 openings selectors d8
  intro d9
  apply bind
  · exact digest_stage_10_success public1 openings selectors d9
  intro d10
  apply bind
  · exact digest_stage_11_success public1 openings selectors d10
  intro d11
  apply bind
  · exact digest_stage_12_success public1 openings selectors d11
  intro d12
  apply bind
  · exact digest_stage_13_success public1 openings selectors d12
  intro d13
  apply bind
  · exact digest_stage_14_success public1 openings selectors d13
  intro d14
  apply bind
  · exact digest_stage_15_success public1 openings selectors d14
  intro d15
  apply bind
  · exact digest_stage_16_success public1 openings selectors d15
  intro d16
  apply bind
  · exact digest_stage_17_success public1 openings selectors d16
  intro d17
  apply bind
  · exact digest_stage_18_success public1 openings selectors d17
  intro d18
  apply bind
  · exact digest_stage_19_success public1 openings selectors d18
  intro d19
  apply bind
  · exact digest_stage_20_success public1 openings selectors d19
  intro d20
  apply bind
  · exact digest_stage_21_success public1 openings selectors d20
  intro d21
  apply bind
  · exact digest_stage_22_success public1 openings selectors d21
  intro d22
  apply bind
  · exact digest_stage_23_success public1 openings selectors d22
  intro d23
  exact digest_stage_24_success public1 openings selectors d23

#print axioms digest_sequence_success
theorem public_digest_success8 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    Success (reference_terminal.public_digest_lanes public1 openings selectors) := by
  rw [digest_factor]
  exact digest_sequence_success public1 openings selectors
#print axioms public_digest_success8
end PV_B3P_Success227
