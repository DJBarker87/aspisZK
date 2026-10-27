import R1Z.PV_CB_ForwardLoop
import R1Z.ProverRwSuccessArithmeticTotal
set_option autoImplicit false
namespace R1Z.PV_CB_ForwardTotal
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal PV_CB_ForwardRange

theorem finite_total {State : Type} (step : Usize → State → Result State)
    (stop : Usize) (step_total : ∀ i, i.val<stop.val → ∀ s,Total (step i s))
    (fuel : Nat) (i : Usize) (state : State) (rank : i.val+fuel=stop.val) :
    Total (PV_CB_ForwardLoop.finite step fuel i state) := by
  induction fuel generalizing i state with
  | zero => exact ok_total _
  | succ fuel ih =>
    have more : i.val<stop.val := by omega
    simp only [PV_CB_ForwardLoop.finite]
    apply bind_total (step_total i more state)
    intro out
    exact ih (advance i) out (by rw [advance_val i stop more];omega)
theorem run_total {State : Type} (step : Usize → State → Result State)
    (stop : Usize) (step_total : ∀ i, i.val<stop.val → ∀ s,Total (step i s))
    (state : State) : Total (PV_CB_ForwardLoop.run step 0#usize stop state) := by
  exact (congrArg ProverRwSuccessArithmeticTotal.Total
    (PV_CB_ForwardLoop.source step stop.val 0#usize stop state (by simp))).mpr
    (finite_total step stop step_total stop.val 0#usize state (by simp))
#print axioms finite_total
#print axioms run_total
end R1Z.PV_CB_ForwardTotal
