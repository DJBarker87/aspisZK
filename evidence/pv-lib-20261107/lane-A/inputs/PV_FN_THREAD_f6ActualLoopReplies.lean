import PV_FN_THREAD_f6LoopReplies
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ActualLoopReplies
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Actual source2097 is ONE arbitrary full reply, with the source-issued
arguments, explicit store, saved loop/caller stacks and exact world/events.
This is the first assume-guarantee stage, prior to contract instantiation. -/
theorem reply2097 {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
     (w : W) (es : List E) (stack : List Config)
    (abstract126 : P PV_FN_THREAD_f6CompletionEntry.fn = none) :
    let s := write (PV_FN_THREAD_f6LoopEntry.prepared t a) ⟨a,18,[]⟩ none
    let c := PV_FN_THREAD_f6LoopEntry.pending t a parents loops
    let wait := PV_THR2_StaticReply.wait s PV_FN_THREAD_f6CompletionEntry.fn [PV_FN_THREAD_f6CompletionEntry.scopeRef a] 17
    let q := PV_THR2_ChildBoundary.delivered B c wait (H wait.request w)
    PV_THR2_IntrinsicState.step B K P H ⟨⟨.running c,w,es⟩,stack⟩ =
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  have ordinary : PV_FN_THREAD_f6CompletionEntry.fn ≠ PV_THR2_Catch219Call318.fn := by
    intro eq
    have ids := congrArg PV_THR2_OffPath.functionId eq
    change (some 126 : Option Nat) = some 318 at ids
    cases ids
  exact PV_FN_THREAD_f6LoopReplies.full_reply B K P H
    (write (PV_FN_THREAD_f6LoopEntry.prepared t a) ⟨a,18,[]⟩ none) a parents loops _ PV_FN_THREAD_f6CompletionEntry.fn [PV_FN_THREAD_f6CompletionEntry.scopeRef a] 17 w es stack abstract126 ordinary

#print axioms reply2097
/-- Actual source2197 is ONE arbitrary full reply, with the source-issued
arguments, explicit store, saved loop/caller stacks and exact world/events.
This is the first assume-guarantee stage, prior to contract instantiation. -/
theorem reply2197 {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (p : Address) (w : W) (es : List E) (stack : List Config)
    (abstract127 : P PV_FN_THREAD_f6LoadCounter.fn = none) :
    let s := write (write (PV_FN_THREAD_f6LoadCounter.prepared t a p) ⟨a,16,[]⟩ none) ⟨a,19,[]⟩ none
    let c := PV_FN_THREAD_f6LoadCounter.pending t a parents loops p
    let wait := PV_THR2_StaticReply.wait s PV_FN_THREAD_f6LoadCounter.fn [PV_FN_THREAD_f6LoadCounter.counterRef p,PV_THR2_KeyValues.pack PV_FN_THREAD_f6LoadCounter.orderingKind []] 15
    let q := PV_THR2_ChildBoundary.delivered B c wait (H wait.request w)
    PV_THR2_IntrinsicState.step B K P H ⟨⟨.running c,w,es⟩,stack⟩ =
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  have ordinary : PV_FN_THREAD_f6LoadCounter.fn ≠ PV_THR2_Catch219Call318.fn := by
    intro eq
    have ids := congrArg PV_THR2_OffPath.functionId eq
    change (some 127 : Option Nat) = some 318 at ids
    cases ids
  exact PV_FN_THREAD_f6LoopReplies.full_reply B K P H
    (write (write (PV_FN_THREAD_f6LoadCounter.prepared t a p) ⟨a,16,[]⟩ none) ⟨a,19,[]⟩ none) a parents loops _ PV_FN_THREAD_f6LoadCounter.fn [PV_FN_THREAD_f6LoadCounter.counterRef p,PV_THR2_KeyValues.pack PV_FN_THREAD_f6LoadCounter.orderingKind []] 15 w es stack abstract127 ordinary

#print axioms reply2197
/-- Actual source2306 is ONE arbitrary full reply, with the source-issued
arguments, explicit store, saved loop/caller stacks and exact world/events.
This is the first assume-guarantee stage, prior to contract instantiation. -/
theorem reply2306 {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
     (w : W) (es : List E) (stack : List Config)
    (abstract126 : P PV_FN_THREAD_f6ParkDeref.fn = none) :
    let s := write (PV_FN_THREAD_f6ParkDeref.prepared t a) ⟨a,23,[]⟩ none
    let c := PV_FN_THREAD_f6ParkDeref.pending t a parents loops
    let wait := PV_THR2_StaticReply.wait s PV_FN_THREAD_f6ParkDeref.fn [PV_FN_THREAD_f6ParkDeref.scopeRef a] 22
    let q := PV_THR2_ChildBoundary.delivered B c wait (H wait.request w)
    PV_THR2_IntrinsicState.step B K P H ⟨⟨.running c,w,es⟩,stack⟩ =
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  have ordinary : PV_FN_THREAD_f6ParkDeref.fn ≠ PV_THR2_Catch219Call318.fn := by
    intro eq
    have ids := congrArg PV_THR2_OffPath.functionId eq
    change (some 126 : Option Nat) = some 318 at ids
    cases ids
  exact PV_FN_THREAD_f6LoopReplies.full_reply B K P H
    (write (PV_FN_THREAD_f6ParkDeref.prepared t a) ⟨a,23,[]⟩ none) a parents loops _ PV_FN_THREAD_f6ParkDeref.fn [PV_FN_THREAD_f6ParkDeref.scopeRef a] 22 w es stack abstract126 ordinary

#print axioms reply2306
/-- Actual source2404 is ONE arbitrary full reply, with the source-issued
arguments, explicit store, saved loop/caller stacks and exact world/events.
This is the first assume-guarantee stage, prior to contract instantiation. -/
theorem reply2404 {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (p : Address) (w : W) (es : List E) (stack : List Config)
    (abstract128 : P PV_FN_THREAD_f6ParkRequest.fn = none) :
    let s := write (PV_FN_THREAD_f6ParkRequest.prepared t a p) ⟨a,21,[]⟩ none
    let c := PV_FN_THREAD_f6ParkRequest.pending t a parents loops p
    let wait := PV_THR2_StaticReply.wait s PV_FN_THREAD_f6ParkRequest.fn [PV_FN_THREAD_f6ParkRequest.threadRef p] 20
    let q := PV_THR2_ChildBoundary.delivered B c wait (H wait.request w)
    PV_THR2_IntrinsicState.step B K P H ⟨⟨.running c,w,es⟩,stack⟩ =
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  have ordinary : PV_FN_THREAD_f6ParkRequest.fn ≠ PV_THR2_Catch219Call318.fn := by
    intro eq
    have ids := congrArg PV_THR2_OffPath.functionId eq
    change (some 128 : Option Nat) = some 318 at ids
    cases ids
  exact PV_FN_THREAD_f6LoopReplies.full_reply B K P H
    (write (PV_FN_THREAD_f6ParkRequest.prepared t a p) ⟨a,21,[]⟩ none) a parents loops _ PV_FN_THREAD_f6ParkRequest.fn [PV_FN_THREAD_f6ParkRequest.threadRef p] 20 w es stack abstract128 ordinary

#print axioms reply2404
/-- Frame of f6's own call issuance; the callee's separate Post supplies its
subsequent caller-cell and memory frame. No native/global world frame inferred. -/
theorem frame2097 (t : Store Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame)  (q : Address)
    (old : q.activation < t.nextActivation) (outside : q.activation ≠ a) :
    (PV_FN_THREAD_f6LoopEntry.pending t a parents loops).store.cells q = t.cells q := by
  have own (i : Nat) : q ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  have fresh (i : Nat) : q ≠ (⟨t.nextActivation,i,[]⟩ : Address) := by
    intro eq
    exact (Nat.ne_of_lt old) (congrArg Address.activation eq)
  simp [PV_FN_THREAD_f6LoopEntry.pending,PV_FN_THREAD_f6LoopEntry.prepared,
    PV_THR2_StaticCall.pending,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,
    write,own,fresh]

#print axioms frame2097
/-- Frame of f6's own call issuance; the callee's separate Post supplies its
subsequent caller-cell and memory frame. No native/global world frame inferred. -/
theorem frame2197 (t : Store Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame) (p : Address) (q : Address)
    (old : q.activation < t.nextActivation) (outside : q.activation ≠ a) :
    (PV_FN_THREAD_f6LoadCounter.pending t a parents loops p).store.cells q = t.cells q := by
  have own (i : Nat) : q ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  have fresh (i : Nat) : q ≠ (⟨t.nextActivation,i,[]⟩ : Address) := by
    intro eq
    exact (Nat.ne_of_lt old) (congrArg Address.activation eq)
  simp [PV_FN_THREAD_f6LoadCounter.pending,PV_FN_THREAD_f6LoadCounter.prepared,
    PV_THR2_StaticCall.pending,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,
    write,own,fresh]

#print axioms frame2197
/-- Frame of f6's own call issuance; the callee's separate Post supplies its
subsequent caller-cell and memory frame. No native/global world frame inferred. -/
theorem frame2306 (t : Store Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame)  (q : Address)
    (old : q.activation < t.nextActivation) (outside : q.activation ≠ a) :
    (PV_FN_THREAD_f6ParkDeref.pending t a parents loops).store.cells q = t.cells q := by
  have own (i : Nat) : q ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  have fresh (i : Nat) : q ≠ (⟨t.nextActivation,i,[]⟩ : Address) := by
    intro eq
    exact (Nat.ne_of_lt old) (congrArg Address.activation eq)
  simp [PV_FN_THREAD_f6ParkDeref.pending,PV_FN_THREAD_f6ParkDeref.prepared,
    PV_THR2_StaticCall.pending,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,
    write,own,fresh]

#print axioms frame2306
/-- Frame of f6's own call issuance; the callee's separate Post supplies its
subsequent caller-cell and memory frame. No native/global world frame inferred. -/
theorem frame2404 (t : Store Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame) (p : Address) (q : Address)
    (old : q.activation < t.nextActivation) (outside : q.activation ≠ a) :
    (PV_FN_THREAD_f6ParkRequest.pending t a parents loops p).store.cells q = t.cells q := by
  have own (i : Nat) : q ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  have fresh (i : Nat) : q ≠ (⟨t.nextActivation,i,[]⟩ : Address) := by
    intro eq
    exact (Nat.ne_of_lt old) (congrArg Address.activation eq)
  simp [PV_FN_THREAD_f6ParkRequest.pending,PV_FN_THREAD_f6ParkRequest.prepared,
    PV_THR2_StaticCall.pending,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,
    write,own,fresh]

#print axioms frame2404
end PV_FN_THREAD_f6ActualLoopReplies
