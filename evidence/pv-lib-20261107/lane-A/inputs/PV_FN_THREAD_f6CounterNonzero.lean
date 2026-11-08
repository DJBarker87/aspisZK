import PV_FN_THREAD_f6CounterBranches
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6CounterNonzero
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Nonzero127 branch executes only its own instructions, stops BEFORE
the actual2306 full-reply call. It does not execute126 or read its internals.
The nonzero discriminant selects this returned127 conclusion branch. -/
theorem nonzero_request {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a n : Nat) (parents : List Frame) (loops : List LoopFrame)
    (b : Bool) (w : W) (es : List E) (stack : List Config)
    (counter_cell : t.cells ⟨a,15,[]⟩ = some (.number n)) (nonzero : n ≠ 0) :
    let u := write (PV_FN_THREAD_f6CounterTest.prepared t a n) ⟨a,14,[]⟩ none
    PV_THR2_IntrinsicState.advance (PV_FN_THREAD_f6CounterTest.carrier base b) ctl P H 12
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block86.drop 12,loops := loops},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (PV_FN_THREAD_f6ParkDeref.pending u a parents loops),w,es⟩,stack⟩ := by
  dsimp only
  rw [show 12 = 4 + 8 from rfl,PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6CounterTest.run base ctl P H t a n parents loops b w es stack counter_cell]
  simp only [PV_FN_THREAD_f6CounterTest.afterBranch,if_neg nonzero,List.nil_append]
  have request := PV_FN_THREAD_f6ParkDeref.run
    (PV_THR2_ScopeLiterals.carrier (PV_FN_THREAD_f6OperatorCarrier.base base)) ctl P H
    (write (PV_FN_THREAD_f6CounterTest.prepared t a n) ⟨a,14,[]⟩ none)
    a parents loops b w es stack
  rw [← PV_FN_THREAD_f6OperatorCarrier.agreement] at request
  exact request

#print axioms nonzero_request
end PV_FN_THREAD_f6CounterNonzero
