import R1Z.PV_RDCD3_CB_ForwardLoop
set_option autoImplicit false
namespace R1Z.PV_RDCD3_CB_FiniteStepEq
open Aeneas Aeneas.Std Result PV_RDCD3_CB_ForwardRange
/-- Step equality is required only on the proved reachable index interval. -/
theorem source {State : Type} (left right : Usize → State → Result State)
    (stop : Usize) (same : ∀ j, j.val<stop.val → ∀ s, left j s = right j s)
    (fuel : Nat) (i : Usize) (state : State) (rank : i.val+fuel=stop.val) :
    PV_RDCD3_CB_ForwardLoop.finite left fuel i state =
      PV_RDCD3_CB_ForwardLoop.finite right fuel i state := by
  induction fuel generalizing i state with
  | zero => rfl
  | succ fuel ih =>
    have inside : i<stop := by change i.val<stop.val; omega
    have step := advance_val i stop inside
    simp only [PV_RDCD3_CB_ForwardLoop.finite,same i (by change i.val<stop.val at inside;exact inside)]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro out hout
    exact ih (advance i) out (by omega)
#print axioms source
end R1Z.PV_RDCD3_CB_FiniteStepEq
