import PV_B3P_Success227
import PV_B3P_CopyLoopSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_copy_terminal_copy_residual (row : reference_copy_terminal.CopyRowExtension) (helper : aspis_core.field.QM31) (chi : aspis_core.field.QM31) :
    Success (reference_copy_terminal.copy_residual row helper chi) := by
  unfold reference_copy_terminal.copy_residual
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply qsub
  intro q1
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply qsub
  intro q3
  apply bind
  · apply index <;> scalar_tac
  intro q4
  apply bind
  · apply qsub
  intro q5
  apply bind
  · apply index <;> scalar_tac
  intro q6
  apply bind
  · apply qsub
  intro q7
  apply bind
  · apply index <;> scalar_tac
  intro q8
  apply bind
  · apply index <;> scalar_tac
  intro q9
  apply bind
  · apply qmul
  intro producer_denominator
  apply bind
  · apply index <;> scalar_tac
  intro q10
  apply bind
  · apply index <;> scalar_tac
  intro q11
  apply bind
  · apply qmul
  intro consumer_denominator
  apply bind
  · apply index <;> scalar_tac
  intro q12
  apply bind
  · apply qmul
  intro q13
  apply bind
  · apply index <;> scalar_tac
  intro q14
  apply bind
  · apply qmul
  intro q15
  apply bind
  · apply qadd
  intro producer_numerator
  apply bind
  · apply index <;> scalar_tac
  intro q16
  apply bind
  · apply qmul
  intro q17
  apply bind
  · apply index <;> scalar_tac
  intro q18
  apply bind
  · apply qmul
  intro q19
  apply bind
  · apply qadd
  intro consumer_numerator
  apply bind
  · apply qmul
  intro q20
  apply bind
  · apply qadd
  intro q21
  apply bind
  · apply qmul
  intro q22
  apply bind
  · apply qmul
  intro q23
  apply qsub

#print axioms total_reference_copy_terminal_copy_residual

/-- Successful execution of the entire actual owned copy evaluator, for
arbitrary field payloads and both public variants. This is not full op227. -/
theorem copy_success (openings : Array aspis_core.field.QM31 16#usize)
    (h1_z : aspis_core.field.QM31) (selectors : reference_copy_terminal.Selectors)
    (lambda chi : aspis_core.field.QM31) (append_index : U64)
    (variant : reference_copy_terminal.PoolV1PairForestCompiledVariantV1) :
    Success (reference_copy_terminal.evaluate_with_selectors openings h1_z selectors lambda chi append_index variant) := by
  unfold reference_copy_terminal.evaluate_with_selectors
  apply bind
  · exact patterns_total openings lambda
  intro patterns
  apply bind
  · exact copy_loop_total selectors append_index variant patterns _ _ _ _ 0#usize
      (by change 0≤136; omega)
  rintro ⟨pv,pw,cv,cw⟩
  apply bind
  · exact active_total selectors
  intro active
  apply bind
  · exact total_reference_copy_terminal_copy_residual _ h1_z chi
  intro residual
  apply bind
  · exact qmul active residual
  intro weighted
  exact ok _

#print axioms copy_success
end PV_B3P_Success227
