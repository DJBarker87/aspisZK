import R1Z.PV_RDCD3_CB_ForwardRange
import R1Z.PV_RDCD3_LoopUnfold
set_option autoImplicit false
namespace R1Z.PV_RDCD3_CB_ForwardLoop
open Aeneas Aeneas.Std Result ControlFlow PV_RDCD3_CB_ForwardRange
variable {State : Type}
def body (step : Usize → State → Result State) (iter : Range) (state : State) :
    Result (ControlFlow (Range × State) State) := do
  if iter.start < iter.end then
    let out ← step iter.start state
    .ok (.cont (between (advance iter.start) iter.end,out))
  else .ok (.done state)
def run (step : Usize → State → Result State) (i stop : Usize) (state : State) :
    Result State :=
  loop (fun (iter,state) => body step iter state) (between i stop,state)
def finite (step : Usize → State → Result State) : Nat → Usize → State → Result State
  | 0,_,state => .ok state
  | fuel+1,i,state => do
    let out ← step i state
    finite step fuel (advance i) out

theorem source (step : Usize → State → Result State) (fuel : Nat) (i stop : Usize)
    (state : State) (rank : i.val+fuel=stop.val) :
    run step i stop state = finite step fuel i state := by
  unfold run
  induction fuel generalizing i state with
  | zero =>
    have done : ¬i<stop := by change ¬i.val<stop.val;omega
    rw [PV_RDCD3_LoopUnfold.loop_bind]
    simp only [body,between,done,if_false,bind_tc_ok,finite]
  | succ fuel ih =>
    have more : i<stop := by change i.val<stop.val;omega
    have value := advance_val i stop more
    rw [PV_RDCD3_LoopUnfold.loop_bind]
    simp only [body,between,more,if_true,bind_assoc_eq,bind_tc_ok,finite]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro out hout
    exact ih (advance i) out (by omega)
#print axioms source
end R1Z.PV_RDCD3_CB_ForwardLoop
