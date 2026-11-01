import NEE_ReachedSubstitution
set_option autoImplicit false
noncomputable section
namespace NEE_ReachedRootModel
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBN_StatementResult
open NED_ValidatorTrace NEE_ValidatorMutation

/-- Ruling-(y) MODEL substitution with every open child law exposed by name.
This theorem does not claim that a Rust child, frame or physical instance has
been proved. The three laws must come from independently accepted bridges. -/
theorem result_and_effects (pay : Pay) (lane : Lane) (late : Late) (s : Statement)
    (payment_bridge : ∀ a, Call.payment a ∈ (NEE_ValidatorOracle.run pay lane late s).2 →
      pay a = NED_ValidatorTrace.payment a)
    (output_lane_bridge : ∀ d, Call.lane d ∈ (NEE_ValidatorOracle.run pay lane late s).2 →
      lane d = NBN_FirstByteDependency.lane enc d)
    (late_bridge : ∀ a out, Call.late a out ∈ (NEE_ValidatorOracle.run pay lane late s).2 →
      ignore (late a out) = ignore (NBN_LateSummary.run enc a out)) :
    NEE_ValidatorOracle.run pay lane late s =
      (pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s,
       (NED_ValidatorTrace.run s).2) := by
  have joined := NEE_ReachedSubstitution.result_and_effects pay lane late s
    (by
      intro c reached
      cases c with
      | payment a => exact payment_bridge a reached
      | lane d => exact output_lane_bridge d reached
      | late a out => exact late_bridge a out reached)
  rw [joined]
  exact Prod.ext (NED_ValidatorTrace.erases s) rfl

#print axioms result_and_effects
end NEE_ReachedRootModel
