import NNE_Dispatch
import RPz7_CPG_RuntimeTrace
set_option autoImplicit false
noncomputable section
namespace NNE_Trace
open Aeneas Aeneas.Std AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
open CPP_BankState Hist_Store
variable {A : Type}
 (n1 : S2W_ExtractionBoundary.First) (n2 m2 : S2W_ExtractionBoundary.Second)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

/-- CPP observes no stage2 reply in its store/event projection. This is valid
for every invocation, including non-selected ASQ8 calls off Root0, stopped
calls, and wrong account counts. No native2=model2 equation is assumed. -/
theorem invocation (store : Store) (input : CPP_Invocation.Invocation A) :
 NNE_Dispatch.view (CPP_Invocation.native n1 n2 copy allocator id store input) =
 NNE_Dispatch.view (CPP_Invocation.native n1 m2 copy allocator id store input) := by
 unfold CPP_Invocation.native
 cases Hiq_ReleaseRoute.route input.call.data <;> rfl

theorem action (bank : Bank) (input : Action A) :
 CPP_BankState.apply n1 n2 copy allocator id bank input =
 CPP_BankState.apply n1 m2 copy allocator id bank input := by
 cases input with
 | invoke input =>
  exact congrArg (fun v : NNE_Dispatch.View => (Bank.mk v.1 bank.lamports,v.2))
   (invocation n1 n2 m2 copy allocator id bank.cells (CPP_BankState.invocation bank input))
 | foreign => rfl
 | credit => rfl
 | reap => rfl
 | rollback => rfl

/-- Complete step transport preserves balances, action identity, store and
physical event. The only changed parameter is stage2, whose reply is ignored. -/
theorem step {before after : Bank} {input : Action A} {event : S2X.AccountEvent}
 (h : CPG_RuntimeTrace.Step n1 n2 copy allocator id before input after event) :
 CPG_RuntimeTrace.Step n1 m2 copy allocator id before input after event := by
 have he := CPG_RuntimeTrace.step_effect h
 rw [action n1 n2 m2 copy allocator id] at he
 have hs := CPG_RuntimeTrace.step_exists n1 m2 copy allocator id before input
 rw [he] at hs
 exact hs

theorem executes {before after : Bank} {inputs : List (Action A)} {events : List S2X.AccountEvent}
 (h : CPG_RuntimeTrace.Executes n1 n2 copy allocator id before inputs after events) :
 CPG_RuntimeTrace.Executes n1 m2 copy allocator id before inputs after events := by
 induction h with
 | nil bank => exact CPG_RuntimeTrace.Executes.nil bank
 | cons head tail ih =>
  exact CPG_RuntimeTrace.Executes.cons (step n1 n2 m2 copy allocator id head) ih
#print axioms invocation
#print axioms action
#print axioms step
#print axioms executes
end NNE_Trace
end
