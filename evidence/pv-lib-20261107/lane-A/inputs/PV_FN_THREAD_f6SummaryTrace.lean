import PV_FN_THREAD_f6ReturnedContinuations
import PV_FN_THREAD_f6CounterNonzero
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6SummaryTrace
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_IntrinsicState (State advance)

/-- A callee's semantic Post at its actual saved call configuration. This
relation is NOT established by the trace constructors. Provider contracts
must establish it, including their explicit store and frame. -/
abbrev CallPost (W E : Type) :=
  Config → W → Store Data → Reply W E Data → Prop

/-- Proof composition, not a replacement interpreter. Own edges are equations
of the unchanged interpreter; each call edge requires its named semantic Post.
In particular an arbitrary Post store alone never licenses a call edge. -/
inductive Trace {W E : Type} (B : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (callee : Nat → CallPost W E) : State W E → State W E → Prop
  | refl (s) : Trace B ctl P H callee s s
  | own (n) (s) : Trace B ctl P H callee s (advance B ctl P H n s)
  | call (site : Nat) (c : Config) (wait : PV_STX2_Native.Waiting Data)
      (post : Store Data) (r : Reply W E Data) (w : W) (es : List E)
      (stack : List Config)
      (waiting : c.frame.waiting = some wait)
      (dependency : callee site c w post r) :
      Trace B ctl P H callee ⟨⟨.running c,w,es⟩,stack⟩
        (let q := PV_FN_THREAD_f6PostStore.deliver B c wait post r
         ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩)
  | trans {s u v} : Trace B ctl P H callee s u →
      Trace B ctl P H callee u v → Trace B ctl P H callee s v

theorem own_eq {W E : Type} (B : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (callee : Nat → CallPost W E) (n : Nat) (s u : State W E)
    (run : advance B ctl P H n s = u) : Trace B ctl P H callee s u := by
  rw [← run]
  exact Trace.own n s

/-- One returned branch of a full-reply call, on the provider's explicit Post
store. The other branches are still admitted by Trace.call without restriction.
The return destination and child slot are actual call-action projections. -/
theorem returned {W E : Type} (B : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (callee : Nat → CallPost W E) (site : Nat)
    (c : Config) (wait : PV_STX2_Native.Waiting Data)
    (post : Store Data) (child dest : Nat) (v : Data)
    (w w' : W) (es suffix : List E) (stack : List Config)
    (waiting : c.frame.waiting = some wait)
    (action : wait.action = .child child (.local dest))
    (dependency : callee site c w post ⟨.returned (.ok v),w',suffix⟩) :
    Trace B ctl P H callee ⟨⟨.running c,w,es⟩,stack⟩
      ⟨⟨.running ⟨{c.frame with waiting := none},c.callers,
        PV_FN_THREAD_f6ReturnedContinuations.resumed post child c.frame.activation dest v⟩,
        w',es ++ suffix⟩,stack⟩ := by
  have edge := Trace.call (B := B) (ctl := ctl) (P := P) (H := H)
    (callee := callee) site c wait post ⟨.returned (.ok v),w',suffix⟩
    w es stack waiting dependency
  dsimp only at edge
  rw [PV_FN_THREAD_f6PostStore.returned B c wait post child dest v w' suffix action] at edge
  exact edge

#print axioms own_eq
#print axioms returned
end PV_FN_THREAD_f6SummaryTrace
