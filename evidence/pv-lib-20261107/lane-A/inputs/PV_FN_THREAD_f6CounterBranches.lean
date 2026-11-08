import PV_FN_THREAD_f6ActualLoopReplies
import PV_FN_THREAD_f6OperatorCarrier
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6CounterBranches
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Zero127 branch exits f6's actual completion loop in five OWN steps.
The zero case is a conclusion branch, not a termination assumption of f6.
The cell equation is an internal projection of the preceding127 Post. -/
theorem zero_exit {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame)
    (afterLoop : List PV_STX2_SliceSyntax.Node) (lower : List LoopFrame)
    (b : Bool) (w : W) (es : List E) (stack : List Config)
    (counter_cell : t.cells ⟨a,15,[]⟩ = some (.number 0)) :
    PV_THR2_IntrinsicState.advance (PV_FN_THREAD_f6CounterTest.carrier base b) ctl P H 5
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block86.drop 12,loops := ⟨PV_THR2_F6.block86,afterLoop⟩ :: lower},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := afterLoop,loops := lower},parents,
        write (PV_FN_THREAD_f6CounterTest.prepared t a 0) ⟨a,14,[]⟩ none⟩,w,es⟩,stack⟩ := by
  rw [show 5 = 4 + 1 from rfl,PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6CounterTest.run base ctl P H t a 0 parents _ b w es stack counter_cell]
  simp only [PV_FN_THREAD_f6CounterTest.afterBranch,if_pos rfl,List.singleton_append,
    PV_THR2_IntrinsicState.advance]
  exact PV_FN_THREAD_f6CounterTest.exit _ ctl P H _ a parents _ lower _ w es stack

/-- Nonzero127 branch executes only its own instructions, then consumes ONE
arbitrary full126 reply at the actual2306 request. Its entire reply domain,
post-world, events, store and saved loop/caller stacks remain in the result.
Full callee contract instantiation is still a separate obligation. -/
theorem nonzero_full_reply {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a n : Nat) (parents : List Frame) (loops : List LoopFrame)
    (b : Bool) (w : W) (es : List E) (stack : List Config)
    (counter_cell : t.cells ⟨a,15,[]⟩ = some (.number n)) (nonzero : n ≠ 0)
    (abstract126 : P PV_FN_THREAD_f6ParkDeref.fn = none) :
    let u := write (PV_FN_THREAD_f6CounterTest.prepared t a n) ⟨a,14,[]⟩ none
    let s := write (PV_FN_THREAD_f6ParkDeref.prepared u a) ⟨a,23,[]⟩ none
    let c := PV_FN_THREAD_f6ParkDeref.pending u a parents loops
    let wait := PV_THR2_StaticReply.wait s PV_FN_THREAD_f6ParkDeref.fn
      [PV_FN_THREAD_f6ParkDeref.scopeRef a] 22
    let q := PV_THR2_ChildBoundary.delivered (PV_FN_THREAD_f6CounterTest.carrier base b) c wait
      (H wait.request w)
    PV_THR2_IntrinsicState.advance (PV_FN_THREAD_f6CounterTest.carrier base b) ctl P H 13
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block86.drop 12,loops := loops},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  dsimp only
  rw [show 13 = 4 + (8 + 1) from rfl,PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6CounterTest.run base ctl P H t a n parents loops b w es stack counter_cell]
  simp only [PV_FN_THREAD_f6CounterTest.afterBranch,if_neg nonzero,List.nil_append]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  have request := PV_FN_THREAD_f6ParkDeref.run
    (PV_THR2_ScopeLiterals.carrier (PV_FN_THREAD_f6OperatorCarrier.base base)) ctl P H
    (write (PV_FN_THREAD_f6CounterTest.prepared t a n) ⟨a,14,[]⟩ none)
    a parents loops b w es stack
  rw [← PV_FN_THREAD_f6OperatorCarrier.agreement] at request
  rw [request]
  simp only [PV_THR2_IntrinsicState.advance]
  exact PV_FN_THREAD_f6ActualLoopReplies.reply2306 _ ctl P H _ a parents loops
    w es stack abstract126

#print axioms zero_exit
#print axioms nonzero_full_reply
end PV_FN_THREAD_f6CounterBranches
