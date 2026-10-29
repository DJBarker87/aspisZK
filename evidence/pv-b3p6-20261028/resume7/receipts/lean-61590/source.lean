import PV_B3P_SemanticCellsSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_terminal_reconstruct_10 (view : Array aspis_core.field.QM31 16#usize) :
    Success (reference_terminal.reconstruct_10 view) := by
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro acc
  apply bind
  · apply qadd
  intro q
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q1
  apply bind
  · apply qadd
  intro acc1
  apply bind
  · apply qadd
  intro q2
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q3
  apply bind
  · apply qadd
  intro acc2
  apply bind
  · apply qadd
  intro q4
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q5
  apply bind
  · apply qadd
  intro acc3
  apply bind
  · apply qadd
  intro q6
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q7
  apply bind
  · apply qadd
  intro acc4
  apply bind
  · apply qadd
  intro q8
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q9
  apply bind
  · apply qadd
  intro acc5
  apply bind
  · apply qadd
  intro q10
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q11
  apply bind
  · apply qadd
  intro acc6
  apply bind
  · apply qadd
  intro q12
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q13
  apply bind
  · apply qadd
  intro acc7
  apply bind
  · apply qadd
  intro q14
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q15
  apply bind
  · apply qadd
  intro acc8
  apply bind
  · apply qadd
  intro q16
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q17
  apply qadd

#print axioms total_reference_terminal_reconstruct_10

theorem total_reference_terminal_add_digest_binding (output : Array aspis_core.field.QM31 8#usize) (selector : aspis_core.field.QM31) (opened : Array aspis_core.field.QM31 16#usize) (start : Std.Usize) (expected : Array aspis_core.field.M31 8#usize) (right_tweak : Bool) (hstart : start.val≤8) :
    Success (reference_terminal.add_digest_binding output selector opened start expected right_tweak) := by
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro m
  apply bind
  · apply tweak_total
  intro target
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q1
  apply bind
  · apply lift_m31_total
  intro q2
  apply bind
  · apply qsub
  intro q3
  apply bind
  · apply qmul
  intro q4
  apply bind
  · apply qadd
  intro q5
  apply bind
  · apply update <;> scalar_tac
  intro output1
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro m1
  apply bind
  · apply tweak_total
  intro target1
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q6
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q7
  apply bind
  · apply lift_m31_total
  intro q8
  apply bind
  · apply qsub
  intro q9
  apply bind
  · apply qmul
  intro q10
  apply bind
  · apply qadd
  intro q11
  apply bind
  · apply update <;> scalar_tac
  intro output2
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro m2
  apply bind
  · apply tweak_total
  intro target2
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q12
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q13
  apply bind
  · apply lift_m31_total
  intro q14
  apply bind
  · apply qsub
  intro q15
  apply bind
  · apply qmul
  intro q16
  apply bind
  · apply qadd
  intro q17
  apply bind
  · apply update <;> scalar_tac
  intro output3
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro m3
  apply bind
  · apply tweak_total
  intro target3
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q18
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q19
  apply bind
  · apply lift_m31_total
  intro q20
  apply bind
  · apply qsub
  intro q21
  apply bind
  · apply qmul
  intro q22
  apply bind
  · apply qadd
  intro q23
  apply bind
  · apply update <;> scalar_tac
  intro output4
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro m4
  apply bind
  · apply tweak_total
  intro target4
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q24
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q25
  apply bind
  · apply lift_m31_total
  intro q26
  apply bind
  · apply qsub
  intro q27
  apply bind
  · apply qmul
  intro q28
  apply bind
  · apply qadd
  intro q29
  apply bind
  · apply update <;> scalar_tac
  intro output5
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro m5
  apply bind
  · apply tweak_total
  intro target5
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q30
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q31
  apply bind
  · apply lift_m31_total
  intro q32
  apply bind
  · apply qsub
  intro q33
  apply bind
  · apply qmul
  intro q34
  apply bind
  · apply qadd
  intro q35
  apply bind
  · apply update <;> scalar_tac
  intro output6
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro m6
  apply bind
  · apply tweak_total
  intro target6
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q36
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q37
  apply bind
  · apply lift_m31_total
  intro q38
  apply bind
  · apply qsub
  intro q39
  apply bind
  · apply qmul
  intro q40
  apply bind
  · apply qadd
  intro q41
  apply bind
  · apply update <;> scalar_tac
  intro output7
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro m7
  apply bind
  · apply tweak_total
  intro target7
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q42
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q43
  apply bind
  · apply lift_m31_total
  intro q44
  apply bind
  · apply qsub
  intro q45
  apply bind
  · apply qmul
  intro q46
  apply bind
  · apply qadd
  intro q47
  apply update <;> scalar_tac

#print axioms total_reference_terminal_add_digest_binding

theorem total_reference_terminal_add_schedule_lanes (packed : Array aspis_core.field.QM31 24#usize) (public1 : reference_terminal.SemanticPublic) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (selectors : reference_copy_terminal.Selectors) :
    Success (reference_terminal.add_schedule_lanes packed public1 openings selectors) := by
  apply bind
  · apply total_reference_terminal_semantic_initial_and_absorption
  rintro ⟨initial, absorption⟩
  apply bind
  · apply preweighted_total <;> scalar_tac
  intro packed1
  apply preweighted_total <;> scalar_tac

#print axioms total_reference_terminal_add_schedule_lanes

theorem total_reference_terminal_path_lanes_literal (path_selector : aspis_core.field.QM31) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    Success (reference_terminal.path_lanes_literal path_selector openings) := by
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro bit
  apply bind
  · apply qsub
  intro q
  apply bind
  · apply qmul
  intro q1
  apply bind
  · apply qmul
  intro q2
  apply bind
  · apply update <;> scalar_tac
  intro path1
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro current
  apply bind
  · apply qsub
  intro q3
  apply bind
  · apply qmul
  intro q4
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q5
  apply bind
  · apply qsub
  intro q6
  apply bind
  · apply qmul
  intro q7
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path2
  apply bind
  · apply qmul
  intro q8
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q9
  apply bind
  · apply qsub
  intro q10
  apply bind
  · apply qmul
  intro q11
  apply lift_total
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path3
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro current1
  apply bind
  · apply qmul
  intro q12
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q13
  apply bind
  · apply qsub
  intro q14
  apply bind
  · apply qmul
  intro q15
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path4
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q16
  apply bind
  · apply qsub
  intro q17
  apply bind
  · apply qmul
  intro q18
  apply lift_total
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path5
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro current2
  apply bind
  · apply qmul
  intro q19
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q20
  apply bind
  · apply qsub
  intro q21
  apply bind
  · apply qmul
  intro q22
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path6
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q23
  apply bind
  · apply qsub
  intro q24
  apply bind
  · apply qmul
  intro q25
  apply lift_total
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path7
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro current3
  apply bind
  · apply qmul
  intro q26
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q27
  apply bind
  · apply qsub
  intro q28
  apply bind
  · apply qmul
  intro q29
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path8
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q30
  apply bind
  · apply qsub
  intro q31
  apply bind
  · apply qmul
  intro q32
  apply lift_total
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path9
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro current4
  apply bind
  · apply qmul
  intro q33
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q34
  apply bind
  · apply qsub
  intro q35
  apply bind
  · apply qmul
  intro q36
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path10
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q37
  apply bind
  · apply qsub
  intro q38
  apply bind
  · apply qmul
  intro q39
  apply lift_total
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path11
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro current5
  apply bind
  · apply qmul
  intro q40
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q41
  apply bind
  · apply qsub
  intro q42
  apply bind
  · apply qmul
  intro q43
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path12
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q44
  apply bind
  · apply qsub
  intro q45
  apply bind
  · apply qmul
  intro q46
  apply lift_total
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path13
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro current6
  apply bind
  · apply qmul
  intro q47
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q48
  apply bind
  · apply qsub
  intro q49
  apply bind
  · apply qmul
  intro q50
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path14
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q51
  apply bind
  · apply qsub
  intro q52
  apply bind
  · apply qmul
  intro q53
  apply lift_total
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path15
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro current7
  apply bind
  · apply qmul
  intro q54
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q55
  apply bind
  · apply qsub
  intro q56
  apply bind
  · apply qmul
  intro q57
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro path16
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q58
  apply bind
  · apply qsub
  intro q59
  apply bind
  · apply qmul
  intro q60
  apply lift_total
  apply lift_total
  apply update <;> scalar_tac

#print axioms total_reference_terminal_path_lanes_literal

theorem total_reference_terminal_add_path_lanes (packed : Array aspis_core.field.QM31 24#usize) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (selectors : reference_copy_terminal.Selectors) :
    Success (reference_terminal.add_path_lanes packed openings selectors) := by
  apply bind
  · apply interval_total <;> scalar_tac
  intro q
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q1
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q2
  apply bind
  · apply qadd
  intro q3
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q4
  apply bind
  · apply qadd
  intro q5
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q6
  apply bind
  · apply qadd
  intro q7
  apply bind
  · apply qmul
  intro path_selector
  apply bind
  · apply total_reference_terminal_path_lanes_literal
  intro path
  apply preweighted_total <;> scalar_tac

#print axioms total_reference_terminal_add_path_lanes

theorem total_reference_terminal_add_value_lanes (packed : Array aspis_core.field.QM31 24#usize) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (selectors : reference_copy_terminal.Selectors) :
    Success (reference_terminal.add_value_lanes packed openings selectors) := by
  apply lift_total
  apply bind
  · apply row_total; first | scalar_tac | (apply row_mul_bound; first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac)) | (apply row_address_bound <;> first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac))
  intro q
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total; first | scalar_tac | (apply row_mul_bound; first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac)) | (apply row_address_bound <;> first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac))
  intro q1
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total; first | scalar_tac | (apply row_mul_bound; first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac)) | (apply row_address_bound <;> first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac))
  intro q2
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q3
  apply bind
  · apply qadd
  intro q4
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q5
  apply bind
  · apply qadd
  intro q6
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q7
  apply bind
  · apply qadd
  intro range_selector
  apply bind
  · apply read_total <;> scalar_tac
  intro q8
  apply bind
  · apply qsquare
  intro q9
  apply bind
  · apply qsub
  intro q10
  apply bind
  · apply update <;> scalar_tac
  intro range1
  apply bind
  · apply read_total <;> scalar_tac
  intro q11
  apply bind
  · apply qsquare
  intro q12
  apply bind
  · apply qsub
  intro q13
  apply bind
  · apply update <;> scalar_tac
  intro range2
  apply bind
  · apply read_total <;> scalar_tac
  intro q14
  apply bind
  · apply qsquare
  intro q15
  apply bind
  · apply qsub
  intro q16
  apply bind
  · apply update <;> scalar_tac
  intro range3
  apply bind
  · apply read_total <;> scalar_tac
  intro q17
  apply bind
  · apply qsquare
  intro q18
  apply bind
  · apply qsub
  intro q19
  apply bind
  · apply update <;> scalar_tac
  intro range4
  apply bind
  · apply read_total <;> scalar_tac
  intro q20
  apply bind
  · apply qsquare
  intro q21
  apply bind
  · apply qsub
  intro q22
  apply bind
  · apply update <;> scalar_tac
  intro range5
  apply bind
  · apply read_total <;> scalar_tac
  intro q23
  apply bind
  · apply qsquare
  intro q24
  apply bind
  · apply qsub
  intro q25
  apply bind
  · apply update <;> scalar_tac
  intro range6
  apply bind
  · apply read_total <;> scalar_tac
  intro q26
  apply bind
  · apply qsquare
  intro q27
  apply bind
  · apply qsub
  intro q28
  apply bind
  · apply update <;> scalar_tac
  intro range7
  apply bind
  · apply read_total <;> scalar_tac
  intro q29
  apply bind
  · apply qsquare
  intro q30
  apply bind
  · apply qsub
  intro q31
  apply bind
  · apply update <;> scalar_tac
  intro range8
  apply bind
  · apply read_total <;> scalar_tac
  intro q32
  apply bind
  · apply qsquare
  intro q33
  apply bind
  · apply qsub
  intro q34
  apply bind
  · apply update <;> scalar_tac
  intro range9
  apply bind
  · apply read_total <;> scalar_tac
  intro q35
  apply bind
  · apply qsquare
  intro q36
  apply bind
  · apply qsub
  intro q37
  apply bind
  · apply update <;> scalar_tac
  intro range10
  apply bind
  · apply read_total <;> scalar_tac
  intro q38
  apply bind
  · apply qsquare
  intro q39
  apply bind
  · apply qsub
  intro q40
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range11
  apply bind
  · apply read_total <;> scalar_tac
  intro q41
  apply bind
  · apply qsquare
  intro q42
  apply bind
  · apply qsub
  intro q43
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range12
  apply bind
  · apply read_total <;> scalar_tac
  intro q44
  apply bind
  · apply qsquare
  intro q45
  apply bind
  · apply qsub
  intro q46
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range13
  apply bind
  · apply read_total <;> scalar_tac
  intro q47
  apply bind
  · apply qsquare
  intro q48
  apply bind
  · apply qsub
  intro q49
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range14
  apply bind
  · apply read_total <;> scalar_tac
  intro q50
  apply bind
  · apply qsquare
  intro q51
  apply bind
  · apply qsub
  intro q52
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range15
  apply bind
  · apply read_total <;> scalar_tac
  intro q53
  apply bind
  · apply qsquare
  intro q54
  apply bind
  · apply qsub
  intro q55
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range16
  apply bind
  · apply read_total <;> scalar_tac
  intro q56
  apply bind
  · apply qsquare
  intro q57
  apply bind
  · apply qsub
  intro q58
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range17
  apply bind
  · apply read_total <;> scalar_tac
  intro q59
  apply bind
  · apply qsquare
  intro q60
  apply bind
  · apply qsub
  intro q61
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range18
  apply bind
  · apply read_total <;> scalar_tac
  intro q62
  apply bind
  · apply qsquare
  intro q63
  apply bind
  · apply qsub
  intro q64
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range19
  apply bind
  · apply read_total <;> scalar_tac
  intro q65
  apply bind
  · apply qsquare
  intro q66
  apply bind
  · apply qsub
  intro q67
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range20
  apply bind
  · apply read_total <;> scalar_tac
  intro q68
  apply bind
  · apply qsquare
  intro q69
  apply bind
  · apply qsub
  intro q70
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range21
  apply bind
  · apply read_total <;> scalar_tac
  intro q71
  apply bind
  · apply qsquare
  intro q72
  apply bind
  · apply qsub
  intro q73
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range22
  apply bind
  · apply read_total <;> scalar_tac
  intro q74
  apply bind
  · apply qsquare
  intro q75
  apply bind
  · apply qsub
  intro q76
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range23
  apply bind
  · apply read_total <;> scalar_tac
  intro q77
  apply bind
  · apply qsquare
  intro q78
  apply bind
  · apply qsub
  intro q79
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range24
  apply bind
  · apply read_total <;> scalar_tac
  intro q80
  apply bind
  · apply qsquare
  intro q81
  apply bind
  · apply qsub
  intro q82
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range25
  apply bind
  · apply read_total <;> scalar_tac
  intro q83
  apply bind
  · apply qsquare
  intro q84
  apply bind
  · apply qsub
  intro q85
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range26
  apply bind
  · apply read_total <;> scalar_tac
  intro q86
  apply bind
  · apply qsquare
  intro q87
  apply bind
  · apply qsub
  intro q88
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range27
  apply bind
  · apply read_total <;> scalar_tac
  intro q89
  apply bind
  · apply qsquare
  intro q90
  apply bind
  · apply qsub
  intro q91
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range28
  apply bind
  · apply read_total <;> scalar_tac
  intro q92
  apply bind
  · apply qsquare
  intro q93
  apply bind
  · apply qsub
  intro q94
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range29
  apply bind
  · apply read_total <;> scalar_tac
  intro q95
  apply bind
  · apply qsquare
  intro q96
  apply bind
  · apply qsub
  intro q97
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro range30
  apply bind
  · apply total_reference_terminal_reconstruct_10
  intro q98
  apply bind
  · apply total_reference_terminal_reconstruct_10
  intro q99
  apply lift_total
  apply bind
  · apply qmul_m31
  intro q100
  apply bind
  · apply qadd
  intro q101
  apply bind
  · apply total_reference_terminal_reconstruct_10
  intro q102
  apply lift_total
  apply bind
  · apply qmul_m31
  intro q103
  apply bind
  · apply qadd
  intro reconstructed
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q104
  apply bind
  · apply qsub
  intro q105
  apply bind
  · apply update <;> scalar_tac
  intro range31
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q106
  apply bind
  · apply update <;> scalar_tac
  intro range32
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q107
  apply bind
  · apply update <;> scalar_tac
  intro range33
  apply bind
  · apply read_total <;> scalar_tac
  intro q108
  apply bind
  · apply qmul
  intro q109
  apply bind
  · apply update <;> scalar_tac
  intro range34
  apply bind
  · apply read_total <;> scalar_tac
  intro q110
  apply bind
  · apply qmul
  intro q111
  apply bind
  · apply update <;> scalar_tac
  intro range35
  apply bind
  · apply read_total <;> scalar_tac
  intro q112
  apply bind
  · apply qmul
  intro q113
  apply bind
  · apply update <;> scalar_tac
  intro range36
  apply bind
  · apply read_total <;> scalar_tac
  intro q114
  apply bind
  · apply qmul
  intro q115
  apply bind
  · apply update <;> scalar_tac
  intro range37
  apply bind
  · apply read_total <;> scalar_tac
  intro q116
  apply bind
  · apply qmul
  intro q117
  apply bind
  · apply update <;> scalar_tac
  intro range38
  apply bind
  · apply read_total <;> scalar_tac
  intro q118
  apply bind
  · apply qmul
  intro q119
  apply bind
  · apply update <;> scalar_tac
  intro range39
  apply bind
  · apply read_total <;> scalar_tac
  intro q120
  apply bind
  · apply qmul
  intro q121
  apply bind
  · apply update <;> scalar_tac
  intro range40
  apply bind
  · apply read_total <;> scalar_tac
  intro q122
  apply bind
  · apply qmul
  intro q123
  apply bind
  · apply update <;> scalar_tac
  intro range41
  apply bind
  · apply read_total <;> scalar_tac
  intro q124
  apply bind
  · apply qmul
  intro q125
  apply bind
  · apply update <;> scalar_tac
  intro range42
  apply bind
  · apply read_total <;> scalar_tac
  intro q126
  apply bind
  · apply qmul
  intro q127
  apply bind
  · apply update <;> scalar_tac
  intro range43
  apply bind
  · apply read_total <;> scalar_tac
  intro q128
  apply bind
  · apply qmul
  intro q129
  apply bind
  · apply update <;> scalar_tac
  intro range44
  apply bind
  · apply read_total <;> scalar_tac
  intro q130
  apply bind
  · apply qmul
  intro q131
  apply bind
  · apply update <;> scalar_tac
  intro range45
  apply bind
  · apply read_total <;> scalar_tac
  intro q132
  apply bind
  · apply qmul
  intro q133
  apply bind
  · apply update <;> scalar_tac
  intro range46
  apply bind
  · apply read_total <;> scalar_tac
  intro q134
  apply bind
  · apply qmul
  intro q135
  apply bind
  · apply update <;> scalar_tac
  intro range47
  apply bind
  · apply read_total <;> scalar_tac
  intro q136
  apply bind
  · apply qmul
  intro q137
  apply bind
  · apply update <;> scalar_tac
  intro range48
  apply bind
  · apply read_total <;> scalar_tac
  intro q138
  apply bind
  · apply qmul
  intro q139
  apply bind
  · apply update <;> scalar_tac
  intro range49
  apply bind
  · apply read_total <;> scalar_tac
  intro q140
  apply bind
  · apply qmul
  intro q141
  apply bind
  · apply update <;> scalar_tac
  intro range50
  apply bind
  · apply read_total <;> scalar_tac
  intro q142
  apply bind
  · apply qmul
  intro q143
  apply bind
  · apply update <;> scalar_tac
  intro range51
  apply bind
  · apply read_total <;> scalar_tac
  intro q144
  apply bind
  · apply qmul
  intro q145
  apply bind
  · apply update <;> scalar_tac
  intro range52
  apply bind
  · apply read_total <;> scalar_tac
  intro q146
  apply bind
  · apply qmul
  intro q147
  apply bind
  · apply update <;> scalar_tac
  intro range53
  apply bind
  · apply read_total <;> scalar_tac
  intro q148
  apply bind
  · apply qmul
  intro q149
  apply bind
  · apply update <;> scalar_tac
  intro range54
  apply bind
  · apply read_total <;> scalar_tac
  intro q150
  apply bind
  · apply qmul
  intro q151
  apply bind
  · apply update <;> scalar_tac
  intro range55
  apply bind
  · apply read_total <;> scalar_tac
  intro q152
  apply bind
  · apply qmul
  intro q153
  apply bind
  · apply update <;> scalar_tac
  intro range56
  apply bind
  · apply read_total <;> scalar_tac
  intro q154
  apply bind
  · apply qmul
  intro q155
  apply bind
  · apply update <;> scalar_tac
  intro range57
  apply bind
  · apply read_total <;> scalar_tac
  intro q156
  apply bind
  · apply qmul
  intro q157
  apply bind
  · apply update <;> scalar_tac
  intro range58
  apply bind
  · apply read_total <;> scalar_tac
  intro q158
  apply bind
  · apply qmul
  intro q159
  apply bind
  · apply update <;> scalar_tac
  intro range59
  apply bind
  · apply read_total <;> scalar_tac
  intro q160
  apply bind
  · apply qmul
  intro q161
  apply bind
  · apply update <;> scalar_tac
  intro range60
  apply bind
  · apply read_total <;> scalar_tac
  intro q162
  apply bind
  · apply qmul
  intro q163
  apply bind
  · apply update <;> scalar_tac
  intro range61
  apply bind
  · apply read_total <;> scalar_tac
  intro q164
  apply bind
  · apply qmul
  intro q165
  apply bind
  · apply update <;> scalar_tac
  intro range62
  apply bind
  · apply read_total <;> scalar_tac
  intro q166
  apply bind
  · apply qmul
  intro q167
  apply bind
  · apply update <;> scalar_tac
  intro range63
  apply bind
  · apply read_total <;> scalar_tac
  intro q168
  apply bind
  · apply qmul
  intro q169
  apply bind
  · apply update <;> scalar_tac
  intro range64
  apply bind
  · apply read_total <;> scalar_tac
  intro q170
  apply bind
  · apply qmul
  intro q171
  apply bind
  · apply update <;> scalar_tac
  intro range65
  apply bind
  · apply read_total <;> scalar_tac
  intro q172
  apply bind
  · apply qmul
  intro q173
  apply bind
  · apply update <;> scalar_tac
  intro range66
  apply bind
  · apply preweighted_total <;> scalar_tac
  intro packed1
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total; first | scalar_tac | (apply row_mul_bound; first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac)) | (apply row_address_bound <;> first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac))
  intro conservation_selector
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q174
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q175
  apply bind
  · apply qsub
  intro q176
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q177
  apply bind
  · apply qsub
  intro q178
  apply bind
  · apply qmul
  intro q179
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q180
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q181
  apply bind
  · apply qsub
  intro q182
  apply bind
  · apply qmul
  intro q183
  apply preweighted_total <;> scalar_tac

#print axioms total_reference_terminal_add_value_lanes

theorem total_reference_terminal_occupancy_lanes_literal (input_occupancy : aspis_core.field.QM31) (output_occupancy : aspis_core.field.QM31) (expected_output : aspis_core.field.M31) (opened : Array aspis_core.field.QM31 16#usize) :
    Success (reference_terminal.occupancy_lanes_literal input_occupancy output_occupancy expected_output opened) := by
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro occupied
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro inverse
  apply bind
  · apply qsub
  intro one_minus
  apply bind
  · apply qadd
  intro both
  apply bind
  · apply qsub
  intro q
  apply bind
  · apply qmul
  intro q1
  apply bind
  · apply qmul
  intro q2
  apply bind
  · apply update <;> scalar_tac
  intro occupancy1
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q3
  apply bind
  · apply qmul
  intro q4
  apply bind
  · apply qsub
  intro q5
  apply bind
  · apply qmul
  intro q6
  apply bind
  · apply update <;> scalar_tac
  intro occupancy2
  apply bind
  · apply qmul
  intro q7
  apply bind
  · apply qmul
  intro q8
  apply bind
  · apply update <;> scalar_tac
  intro occupancy3
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q9
  apply bind
  · apply qmul
  intro q10
  apply bind
  · apply qmul
  intro q11
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro occupancy4
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q12
  apply bind
  · apply qmul
  intro q13
  apply bind
  · apply qmul
  intro q14
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro occupancy5
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q15
  apply bind
  · apply qmul
  intro q16
  apply bind
  · apply qmul
  intro q17
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro occupancy6
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q18
  apply bind
  · apply qmul
  intro q19
  apply bind
  · apply qmul
  intro q20
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro occupancy7
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q21
  apply bind
  · apply qmul
  intro q22
  apply bind
  · apply qmul
  intro q23
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro occupancy8
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q24
  apply bind
  · apply qmul
  intro q25
  apply bind
  · apply qmul
  intro q26
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro occupancy9
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q27
  apply bind
  · apply qmul
  intro q28
  apply bind
  · apply qmul
  intro q29
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro occupancy10
  apply lift_total
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q30
  apply bind
  · apply qmul
  intro q31
  apply bind
  · apply qmul
  intro q32
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro occupancy11
  apply bind
  · apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))
  intro q33
  apply bind
  · apply qmul
  intro q34
  apply bind
  · apply qmul
  intro q35
  apply bind
  · apply lift_m31_total
  intro q36
  apply bind
  · apply qsub
  intro q37
  apply bind
  · apply qmul
  intro q38
  apply bind
  · apply qadd
  intro q39
  apply update <;> scalar_tac

#print axioms total_reference_terminal_occupancy_lanes_literal

theorem total_reference_terminal_add_occupancy_lanes (packed : Array aspis_core.field.QM31 24#usize) (public1 : reference_terminal.SemanticPublic) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (selectors : reference_copy_terminal.Selectors) :
    Success (reference_terminal.add_occupancy_lanes packed public1 openings selectors) := by
  apply input_row_bind
  apply bind
  · apply row_total; first | scalar_tac | (apply row_mul_bound; first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac)) | (apply row_address_bound <;> first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac))
  intro input_occupancy
  apply output_row_bind
  apply bind
  · apply row_total; first | scalar_tac | (apply row_mul_bound; first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac)) | (apply row_address_bound <;> first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac))
  intro output_occupancy
  apply bind
  · apply variant_output_total
  intro expected_output
  apply bind
  · apply total_reference_terminal_occupancy_lanes_literal
  intro occupancy
  apply preweighted_total <;> scalar_tac

#print axioms total_reference_terminal_add_occupancy_lanes

end PV_B3P_Success227
