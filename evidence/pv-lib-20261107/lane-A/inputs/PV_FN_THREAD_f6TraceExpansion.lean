import PV_FN_THREAD_f6SummaryTrace
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6TraceExpansion
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6SummaryTrace PV_THR2_IntrinsicState

/-- The required implementation adapter for a call Post: the provider's
body actually executes from the source-issued waiting configuration to the
explicit Post delivery. This is a named proof obligation, NOT a native or
endpoint assumption. A predicate describing attractive stores cannot discharge
it. Prefix events and arbitrary caller/intrinsic stacks are quantified here. -/
def Implements {W E : Type} (B : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (C : Nat → CallPost W E) : Prop :=
  ∀ (site : Nat) (c : Config) (wait : PV_STX2_Native.Waiting Data)
    (post : Store Data) (r : Reply W E Data) (w : W) (es : List E) (stack : List Config),
    c.frame.waiting = some wait → C site c w post r →
    ∃ n, advance B ctl P H n ⟨⟨.running c,w,es⟩,stack⟩ =
      (let q := PV_FN_THREAD_f6PostStore.deliver B c wait post r
       ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩)

/-- Expand a finite assume-guarantee composition into the unchanged interpreter.
The caller's own administrative steps and the callee's implementation steps are
added; no equal-fuel claim, body-store erasure or resolver change is used.
This generic join does not establish any concrete Implements instance. -/
theorem expand {W E : Type} (B : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (C : Nat → CallPost W E) (callee_implementations : Implements B ctl P H C)
    (s u : State W E) (trace : Trace B ctl P H C s u) :
    ∃ n, advance B ctl P H n s = u := by
  induction trace with
  | refl s => exact ⟨0,rfl⟩
  | own n s => exact ⟨n,rfl⟩
  | call site c wait post r w es stack waiting dependency =>
    exact callee_implementations site c wait post r w es stack waiting dependency
  | trans first second ih1 ih2 =>
    obtain ⟨n,hn⟩ := ih1
    obtain ⟨m,hm⟩ := ih2
    refine ⟨n+m,?_⟩
    rw [PV_THR2_IntrinsicComposition.advance_add,hn,hm]

#print axioms expand
end PV_FN_THREAD_f6TraceExpansion
