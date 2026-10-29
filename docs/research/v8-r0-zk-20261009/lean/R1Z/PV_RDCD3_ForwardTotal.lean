import R1Z.PV_RDCD3_CB_ForwardLoop
import R1Z.PV_RDCD3_Total
set_option autoImplicit false
namespace R1Z.PV_RDCD3_ForwardTotal
open Aeneas Aeneas.Std Result PV_RDCD3_Total PV_RDCD3_CB_ForwardRange
/-- All iterations are proved on their reachable interval; no iteration is
executed by kernel reduction to establish this statement. -/
theorem finite_total {State : Type} (step : Usize → State → Result State)
    (stop : Usize) (safe : ∀ i, i.val<stop.val → ∀ state, Total (step i state))
    (fuel : Nat) (i : Usize) (state : State) (rank : i.val+fuel=stop.val) :
    Total (PV_RDCD3_CB_ForwardLoop.finite step fuel i state) := by
  induction fuel generalizing i state with
  | zero => exact ok_total state
  | succ fuel ih =>
    have more : i<stop := by change i.val<stop.val;omega
    have advance := advance_val i stop more
    obtain ⟨next,hnext⟩ := safe i (by change i.val<stop.val at more;exact more) state
    obtain ⟨out,hout⟩ := ih (PV_RDCD3_CB_ForwardRange.advance i) next (by omega)
    refine ⟨out,?_⟩
    simp only [PV_RDCD3_CB_ForwardLoop.finite,hnext,bind_tc_ok,hout]
#print axioms finite_total
end R1Z.PV_RDCD3_ForwardTotal
