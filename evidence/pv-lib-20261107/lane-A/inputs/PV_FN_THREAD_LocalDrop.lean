import PV_THR2_IntrinsicAtContinuation
import PV_THR2_IntrinsicCompatible
import PV_THR2_ChildBoundary
set_option autoImplicit false
namespace PV_FN_THREAD_LocalDrop
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- A source Drop request retains its actual continuation and complete store.
Unlike a function call, it mints no child activation. -/
def wait (slot : Nat) (fn value : Data) : PV_STX2_Native.Waiting Data :=
  ⟨.drop fn value,.dropped (.local slot),[]⟩
def pending (s : Store Data) (a slot : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (fn value : Data) : Config :=
  ⟨{activation := a,remaining := rest,loops := loops,waiting := some (wait slot fn value)},parents,s⟩
def steps {W : Type} (_B : Carrier W Data) (s : Store Data) (a slot : Nat) : Nat :=
  1 + match s.cells ⟨a,slot,[]⟩ with | none => 0 | some _ => 1
def after {W E : Type} (B : Carrier W Data)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a slot : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (site : Site) (fn : Data) (conditional : Bool)
    (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  match s.cells ⟨a,slot,[]⟩ with
  | none => if conditional then
      ⟨⟨.running ⟨{activation := a,remaining := rest,loops := loops},parents,s⟩,w,es⟩,stack⟩
    else ⟨⟨.undefined (some site) s,w,es⟩,stack⟩
  | some value =>
    let r := PV_THR2_ChildBoundary.delivered B (pending s a slot parents loops rest fn value)
      (wait slot fn value) (H (.drop fn value) w)
    ⟨⟨r.status,r.world,es ++ r.events⟩,stack⟩
/-- Generic source-only Drop issue. No reply or success assumption. -/
theorem issue {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a slot : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (site : Site) (fn value : Data) (conditional : Bool)
    (w : W) (es : List E) (stack : List Config) (cell : s.cells ⟨a,slot,[]⟩ = some value) :
    PV_THR2_IntrinsicState.advance B K P H 1
      ⟨⟨.running ⟨{activation := a,remaining := .leaf (.drop site (.local slot) fn conditional []) :: rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (pending s a slot parents loops rest fn value),w,es⟩,stack⟩ := by
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_GapCompletion.step,
    PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,native,adopt,
    PV_STX2_Native.step,PV_STX2_Store.read,cell,pending,wait]
/-- Exact arbitrary full reply at the saved Drop request. The resolver never
enters drop-glue code; every failure and pending answer remains a world answer. -/
theorem receive {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a slot : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (fn value : Data)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance B K P H 1
      ⟨⟨.running (pending s a slot parents loops rest fn value),w,es⟩,stack⟩ =
      let r := PV_THR2_ChildBoundary.delivered B (pending s a slot parents loops rest fn value)
        (wait slot fn value) (H (.drop fn value) w)
      ⟨⟨r.status,r.world,es ++ r.events⟩,stack⟩ := by
  simp only [PV_THR2_IntrinsicState.advance]
  rw [PV_THR2_IntrinsicCompatible.step B K P H _ w es stack (by rfl)]
  cases answer : (H (.drop fn value) w).answer with
  | pending =>
    simp [PV_THR2_Execution.step,PV_THR2_Dynamic.active,pending,wait,answer,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_ChildBoundary.delivered,native,adopt,
    PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,
    PV_STX2_Native.storeResult,locate,writeAddress,PV_STX2_Pinned.eraseFault]
  | fault f =>
    cases f <;> cases config : PV_STX2_PinnedConfig <;> cases parents <;>
      simp [PV_THR2_Execution.step,PV_THR2_Dynamic.active,pending,wait,answer,config,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_ChildBoundary.delivered,native,adopt,
    PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,
    PV_STX2_Native.storeResult,locate,writeAddress,PV_STX2_Pinned.eraseFault]
  | returned result =>
    cases result <;> cases parents <;>
      simp [PV_THR2_Execution.step,PV_THR2_Dynamic.active,pending,wait,answer,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_ChildBoundary.delivered,native,adopt,
    PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,
    PV_STX2_Native.storeResult,locate,writeAddress,PV_STX2_Pinned.eraseFault]
#print axioms issue
#print axioms receive
end PV_FN_THREAD_LocalDrop
