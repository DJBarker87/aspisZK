import PV_B3P_Success227
import PV_B3P_P227_12
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_terminal_equality_factor (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) :
    Success (reference_terminal.equality_factor a b) := by
  unfold reference_terminal.equality_factor
  apply bind
  · apply qmul
  intro ab
  apply bind
  · apply qsub
  intro q
  apply bind
  · apply qsub
  intro q1
  apply bind
  · apply qadd
  intro q2
  apply qadd

#print axioms total_reference_terminal_equality_factor

theorem total_reference_terminal_equality_value (left : Array aspis_core.field.QM31 10#usize) (right : Array aspis_core.field.QM31 10#usize) :
    Success (reference_terminal.equality_value left right) := by
  unfold reference_terminal.equality_value
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply index <;> scalar_tac
  intro q1
  apply bind
  · apply total_reference_terminal_equality_factor
  intro product
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply index <;> scalar_tac
  intro q3
  apply bind
  · apply total_reference_terminal_equality_factor
  intro q4
  apply bind
  · apply qmul
  intro product1
  apply bind
  · apply index <;> scalar_tac
  intro q5
  apply bind
  · apply index <;> scalar_tac
  intro q6
  apply bind
  · apply total_reference_terminal_equality_factor
  intro q7
  apply bind
  · apply qmul
  intro product2
  apply bind
  · apply index <;> scalar_tac
  intro q8
  apply bind
  · apply index <;> scalar_tac
  intro q9
  apply bind
  · apply total_reference_terminal_equality_factor
  intro q10
  apply bind
  · apply qmul
  intro product3
  apply bind
  · apply index <;> scalar_tac
  intro q11
  apply bind
  · apply index <;> scalar_tac
  intro q12
  apply bind
  · apply total_reference_terminal_equality_factor
  intro q13
  apply bind
  · apply qmul
  intro product4
  apply bind
  · apply index <;> scalar_tac
  intro q14
  apply bind
  · apply index <;> scalar_tac
  intro q15
  apply bind
  · apply total_reference_terminal_equality_factor
  intro q16
  apply bind
  · apply qmul
  intro product5
  apply bind
  · apply index <;> scalar_tac
  intro q17
  apply bind
  · apply index <;> scalar_tac
  intro q18
  apply bind
  · apply total_reference_terminal_equality_factor
  intro q19
  apply bind
  · apply qmul
  intro product6
  apply bind
  · apply index <;> scalar_tac
  intro q20
  apply bind
  · apply index <;> scalar_tac
  intro q21
  apply bind
  · apply total_reference_terminal_equality_factor
  intro q22
  apply bind
  · apply qmul
  intro product7
  apply bind
  · apply index <;> scalar_tac
  intro q23
  apply bind
  · apply index <;> scalar_tac
  intro q24
  apply bind
  · apply total_reference_terminal_equality_factor
  intro q25
  apply bind
  · apply qmul
  intro product8
  apply bind
  · apply index <;> scalar_tac
  intro q26
  apply bind
  · apply index <;> scalar_tac
  intro q27
  apply bind
  · apply total_reference_terminal_equality_factor
  intro q28
  apply qmul

#print axioms total_reference_terminal_equality_value

end PV_B3P_Success227
