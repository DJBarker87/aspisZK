import NEM_LateOracle
set_option autoImplicit false
noncomputable section
namespace NEM_ValidatorComposed
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBN_StatementResult

/-- Concrete model G for the three SAME calls certified natively. The hybrid
native correspondence is checked separately by NEM_validate; this theorem
introduces no inner callee domain, interpretation, or bridge hypothesis. -/
theorem result_state_effects {State : Type} (s : Statement) (state : State) :
    let observed := NEE_ValidatorOracle.run NEM_PaymentReached.pay NEM_LaneReached.lane
      NEM_LateOracle.late s
    (observed.1,state,observed.2) =
      (pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s,
       state,(NED_ValidatorTrace.run s).2) := by
  have same := NEE_ReachedRootModel.result_and_effects NEM_PaymentReached.pay
    NEM_LaneReached.lane NEM_LateOracle.late s
    (fun a reached => NEM_PaymentReached.payment_reached NEM_LaneReached.lane
      NEM_LateOracle.late s a reached)
    (fun d reached => NEM_LaneReached.lane_reached NEM_LateOracle.late s d reached)
    (fun a out reached => NEM_LateOracle.late_reached s a out reached)
  rw [same]

#print axioms result_state_effects
end NEM_ValidatorComposed
