import PV_B3P_Success227
import PV_B3P_SemanticBasicsSuccess227
import PV_B3P_PureBind227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_terminal_absorption_lanes_literal (low : aspis_core.field.QM31) (fixed : aspis_core.field.QM31) (chunk_two : aspis_core.field.QM31) (chunk_eight : aspis_core.field.QM31) (nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) :
    Success (reference_terminal.absorption_lanes_literal low fixed chunk_two chunk_eight nodes openings) := by
  unfold reference_terminal.absorption_lanes_literal
  apply bind
  · apply read_total <;> scalar_tac
  intro q
  apply bind
  · apply absorption_lane_total
  intro q1
  apply bind
  · apply update <;> scalar_tac
  intro output1
  apply bind
  · apply read_total <;> scalar_tac
  intro q2
  apply bind
  · apply absorption_lane_total
  intro q3
  apply bind
  · apply update <;> scalar_tac
  intro output2
  apply bind
  · apply read_total <;> scalar_tac
  intro q4
  apply bind
  · apply absorption_lane_total
  intro q5
  apply bind
  · apply update <;> scalar_tac
  intro output3
  apply bind
  · apply read_total <;> scalar_tac
  intro q6
  apply bind
  · apply absorption_lane_total
  intro q7
  apply bind
  · apply update <;> scalar_tac
  intro output4
  apply bind
  · apply read_total <;> scalar_tac
  intro q8
  apply bind
  · apply absorption_lane_total
  intro q9
  apply bind
  · apply update <;> scalar_tac
  intro output5
  apply bind
  · apply read_total <;> scalar_tac
  intro q10
  apply bind
  · apply absorption_lane_total
  intro q11
  apply bind
  · apply update <;> scalar_tac
  intro output6
  apply bind
  · apply read_total <;> scalar_tac
  intro q12
  apply bind
  · apply absorption_lane_total
  intro q13
  apply bind
  · apply update <;> scalar_tac
  intro output7
  apply bind
  · apply read_total <;> scalar_tac
  intro q14
  apply bind
  · apply absorption_lane_total
  intro q15
  apply bind
  · apply update <;> scalar_tac
  intro output8
  apply bind
  · apply read_total <;> scalar_tac
  intro q16
  apply bind
  · apply absorption_lane_total
  intro q17
  apply bind
  · apply update <;> scalar_tac
  intro output9
  apply bind
  · apply read_total <;> scalar_tac
  intro q18
  apply bind
  · apply absorption_lane_total
  intro q19
  apply bind
  · apply update <;> scalar_tac
  intro output10
  apply bind
  · apply read_total <;> scalar_tac
  intro q20
  apply bind
  · apply absorption_lane_total
  intro q21
  apply bind
  · apply update <;> scalar_tac
  intro output11
  apply bind
  · apply read_total <;> scalar_tac
  intro q22
  apply bind
  · apply absorption_lane_total
  intro q23
  apply bind
  · apply update <;> scalar_tac
  intro output12
  apply bind
  · apply read_total <;> scalar_tac
  intro q24
  apply bind
  · apply absorption_lane_total
  intro q25
  apply bind
  · apply update <;> scalar_tac
  intro output13
  apply bind
  · apply read_total <;> scalar_tac
  intro q26
  apply bind
  · apply absorption_lane_total
  intro q27
  apply bind
  · apply update <;> scalar_tac
  intro output14
  apply bind
  · apply read_total <;> scalar_tac
  intro q28
  apply bind
  · apply absorption_lane_total
  intro q29
  apply bind
  · apply update <;> scalar_tac
  intro output15
  apply bind
  · apply read_total <;> scalar_tac
  intro q30
  apply bind
  · apply absorption_lane_total
  intro q31
  apply update <;> scalar_tac

#print axioms total_reference_terminal_absorption_lanes_literal

theorem total_reference_terminal_semantic_initial_and_absorption (public1 : reference_terminal.SemanticPublic) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (selectors : reference_copy_terminal.Selectors) :
    Success (reference_terminal.semantic_initial_and_absorption public1 openings selectors) := by
  unfold reference_terminal.semantic_initial_and_absorption
  have rate8 : aspis_statement.poseidon2.RATE.val=8 := by unfold aspis_statement.poseidon2.RATE; rfl
  have rate9 : (Usize.wrapping_add aspis_statement.poseidon2.RATE 1#usize).val=9 := by
    have h := PV_B3P_Offset226V3.add_value aspis_statement.poseidon2.RATE 1#usize (by have hsize := usize_1024_size; change aspis_statement.poseidon2.RATE.val+1 < _; omega)
    simpa only [rate8,show (1#usize).val=1 from rfl] using h
  apply bind
  · apply interval_total <;> scalar_tac
  intro q
  apply bind
  · apply interval_total <;> scalar_tac
  intro nodes
  apply bind
  · apply index <;> scalar_tac
  intro q1
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply qadd
  intro q3
  apply bind
  · apply index <;> scalar_tac
  intro q4
  apply bind
  · apply qadd
  intro q5
  apply bind
  · apply index <;> scalar_tac
  intro q6
  apply bind
  · apply qadd
  intro first_common
  apply bind
  · apply index <;> scalar_tac
  intro q7
  apply bind
  · apply index <;> scalar_tac
  intro q8
  apply bind
  · apply index <;> scalar_tac
  intro q9
  apply bind
  · apply initial_variant_total
  intro pair
  rcases pair with ⟨transfer_first, fixed, private_chunk_eight, private_chunk_two⟩
  apply bind
  · apply index <;> scalar_tac
  intro q10
  apply bind
  · apply qadd
  intro q11
  apply bind
  · apply qadd
  intro q12
  apply bind
  · apply qmul
  intro full_initial_selector
  apply bind
  · apply qmul
  intro rate_initial_selector
  apply bind
  · apply total_host_terminal_field_PreparedQm31Multiplier_new
  intro full
  apply bind
  · apply qadd
  intro q13
  apply bind
  · apply total_host_terminal_field_PreparedQm31Multiplier_new
  intro full_or_rate
  apply bind
  · apply read_total <;> scalar_tac
  intro q14
  apply bind
  · apply initial_lane_total
  intro q15
  apply bind
  · apply update <;> scalar_tac
  intro output1
  apply bind
  · apply read_total <;> scalar_tac
  intro q16
  apply bind
  · apply initial_lane_total
  intro q17
  apply bind
  · apply update <;> scalar_tac
  intro output2
  apply bind
  · apply read_total <;> scalar_tac
  intro q18
  apply bind
  · apply initial_lane_total
  intro q19
  apply bind
  · apply update <;> scalar_tac
  intro output3
  apply bind
  · apply read_total <;> scalar_tac
  intro q20
  apply bind
  · apply initial_lane_total
  intro q21
  apply bind
  · apply update <;> scalar_tac
  intro output4
  apply bind
  · apply read_total <;> scalar_tac
  intro q22
  apply bind
  · apply initial_lane_total
  intro q23
  apply bind
  · apply update <;> scalar_tac
  intro output5
  apply bind
  · apply read_total <;> scalar_tac
  intro q24
  apply bind
  · apply initial_lane_total
  intro q25
  apply bind
  · apply update <;> scalar_tac
  intro output6
  apply bind
  · apply read_total <;> scalar_tac
  intro q26
  apply bind
  · apply initial_lane_total
  intro q27
  apply bind
  · apply update <;> scalar_tac
  intro output7
  apply bind
  · apply read_total <;> scalar_tac
  intro q28
  apply bind
  · apply initial_lane_total
  intro q29
  apply bind
  · apply update <;> scalar_tac
  intro output8
  apply bind
  · apply read_total <;> scalar_tac
  intro q30
  apply bind
  · apply initial_lane_total
  intro q31
  apply bind
  · apply update <;> scalar_tac
  intro output9
  apply bind
  · apply read_total <;> scalar_tac
  intro q32
  apply bind
  · apply initial_lane_total
  intro q33
  apply bind
  · apply update <;> scalar_tac
  intro output10
  apply bind
  · apply read_total <;> scalar_tac
  intro q34
  apply bind
  · apply initial_lane_total
  intro q35
  apply bind
  · apply update <;> scalar_tac
  intro output11
  apply bind
  · apply read_total <;> scalar_tac
  intro q36
  apply bind
  · apply initial_lane_total
  intro q37
  apply bind
  · apply update <;> scalar_tac
  intro output12
  apply bind
  · apply read_total <;> scalar_tac
  intro q38
  apply bind
  · apply initial_lane_total
  intro q39
  apply bind
  · apply update <;> scalar_tac
  intro output13
  apply bind
  · apply read_total <;> scalar_tac
  intro q40
  apply bind
  · apply initial_lane_total
  intro q41
  apply bind
  · apply update <;> scalar_tac
  intro output14
  apply bind
  · apply read_total <;> scalar_tac
  intro q42
  apply bind
  · apply initial_lane_total
  intro q43
  apply bind
  · apply update <;> scalar_tac
  intro output15
  apply bind
  · apply read_total <;> scalar_tac
  intro q44
  apply bind
  · apply initial_lane_total
  intro q45
  apply bind
  · apply update <;> scalar_tac
  intro output16
  apply bind
  · apply qadd
  intro q46
  apply bind
  · apply qadd
  intro note_first
  apply bind
  · apply qmul_m31
  intro q47
  apply bind
  · apply qmul_m31
  intro q48
  apply bind
  · apply qadd
  intro q49
  apply bind
  · apply qmul_m31
  intro q50
  apply bind
  · apply qadd
  intro domain
  apply bind
  · apply qmul_m31
  intro q51
  apply bind
  · apply qmul_m31
  intro q52
  apply bind
  · apply qadd
  intro q53
  apply bind
  · apply qmul_m31
  intro q54
  apply bind
  · apply qadd
  intro length
  apply bind
  · apply index <;> scalar_tac
  intro q55
  apply bind
  · apply qmul
  intro q56
  apply bind
  · apply qsub
  intro q57
  apply bind
  · apply update <;> scalar_tac
  intro output17
  rw [PV_B3P_PureBind227.lift_bind]
  apply bind
  · apply index <;> scalar_tac
  intro q58
  apply bind
  · apply qmul
  intro q59
  apply bind
  · apply qsub
  intro q60
  rw [PV_B3P_PureBind227.lift_bind]
  apply bind
  · apply update <;> scalar_tac
  intro output18
  apply bind
  · apply qadd
  intro q61
  apply bind
  · apply index <;> scalar_tac
  intro q62
  apply bind
  · apply qadd
  intro q63
  apply bind
  · apply qadd
  intro q64
  apply bind
  · apply index <;> scalar_tac
  intro q65
  apply bind
  · apply qadd
  intro q66
  apply bind
  · apply qadd
  intro q67
  apply bind
  · apply index <;> scalar_tac
  intro q68
  apply bind
  · apply qadd
  intro chunk_eight
  apply bind
  · apply index <;> scalar_tac
  intro q69
  apply bind
  · apply index <;> scalar_tac
  intro q70
  apply bind
  · apply qadd
  intro chunk_two
  apply bind
  · apply qadd
  intro chunk_eight1
  apply bind
  · apply qadd
  intro chunk_two1
  apply bind
  · apply index <;> scalar_tac
  intro q71
  apply bind
  · apply total_reference_terminal_absorption_lanes_literal
  intro absorption
  exact ok _

#print axioms total_reference_terminal_semantic_initial_and_absorption

end PV_B3P_Success227
