import R1Z.PV_ROWS10B_Audit
set_option autoImplicit false
namespace R1Z.PV_ROWS10B_Replay
open Aeneas Aeneas.Std PV_ROWS10B_Consumed PV_ROWS10B_ControlWord
/-- Frozen focused closure plus a negative control: a short finite prefix
and an infinite retry word have distinct, explicitly proved meanings. -/
theorem prefix_and_infinite :
    run [⟨-1,4⟩] 64 = .pending 64 ∧ Diverges (fun _ => ⟨-1,4⟩) 64 :=
  ⟨short_tape_is_pending, PV_ROWS10B_Retry.perpetual_eintr⟩
/-- Outer failure has not been collapsed into the option-B OS-error signal. -/
theorem outer_failure_distinct :
    stop (.fail .panic : Result ((core.result.Result Unit Unit) × Slice U8)) ≠
      .returned true := by intro h; cases h
/-- Divergence has not been collapsed into either OS success or OS failure. -/
theorem divergence_distinct (error : Bool) :
    stop (.div : Result ((core.result.Result Unit Unit) × Slice U8)) ≠
      .returned error := by intro h; cases h
#print axioms prefix_and_infinite
#print axioms outer_failure_distinct
#print axioms divergence_distinct
end R1Z.PV_ROWS10B_Replay
