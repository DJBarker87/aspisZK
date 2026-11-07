import PV_FN_THREAD_f6EarlyControl
import PV_FN_THREAD_f6CompletionPropagation
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6DivergenceBoundary
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces

/-- The selected source carrier/control, with only the first native leaf
resolved as CHILD. Every later source resolver disposition is retained. -/
def machine {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data) : Machine E :=
  ⟨PV_THR2_OwnInitExactReturnedCases.carrier C b,PV_THR2_Scalars.control K,
    PV_FN_THREAD_f6Reply121.programs P,H⟩

def pending {E : Type} (x : Entry E) :=
  PV_THR2_ScopeCall121.pending (PV_THR2_ScopePrologue.prepared x.store x.activation)
    x.activation (x.parent :: x.parents)

def reply {E : Type} (x : Entry E)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data) :=
  H (.child PV_THR2_ScopeCall121.fn x.store.nextActivation [.number 0]) x.world

def at18 {E : Type} (x : Entry E)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data) : PV_THR2_IntrinsicState.State OWNER E :=
  let c := pending x
  let r := reply x H
  ⟨⟨.running {c with frame := {c.frame with completed := some .div}},
    r.world,x.events ++ r.events⟩,x.suspended⟩

def at19 {E : Type} (x : Entry E)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data) : PV_THR2_IntrinsicState.State OWNER E :=
  let r := reply x H
  ⟨⟨.running ⟨{x.parent with completed := some .div},x.parents,(pending x).store⟩,
    r.world,x.events ++ r.events⟩,x.suspended⟩

/-- Consume the existing own-entry/first-call certificate at its actual div
reply. No constructor124 or other provider body is executed. -/
theorem entry_div (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    {E : Type} (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (x : Entry E) (body : x.body = PV_THR2_F6.live)
    (diverged : (reply x H).answer = .returned .div) :
    PV_FN_THREAD_f6Interfaces.run (machine C b K P H) x 18 = at18 x H := by
  unfold PV_FN_THREAD_f6Interfaces.run entry
  rw [body]
  dsimp only [machine,PV_THR2_OwnInitExactReturnedCases.carrier]
  rw [PV_FN_THREAD_f6Reply121.from_entry (PV_THR2_RangeLiterals.carrier C)
    K P H x.store x.activation (x.parent :: x.parents) b x.world x.events x.suspended]
  have counter : (PV_THR2_ScopePrologue.prepared x.store x.activation).nextActivation =
      x.store.nextActivation := rfl
  have divH : (H (.child PV_THR2_ScopeCall121.fn x.store.nextActivation [.number 0])
      x.world).answer = .returned .div := diverged
  simp [PV_THR2_ChildBoundary.delivered,PV_STX2_Pinned.reply,
    PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,PV_STX2_SliceMachine.adopt,
    counter,divH,at18,pending,reply,PV_THR2_ScopeCall121.pending,PV_THR2_StaticCall.pending]

/-- An actual one-argument saved call cannot select the three-argument catch
intrinsic, regardless of its callee token or completion marker. -/
theorem single_no_catch (c : Config) (wait : PV_STX2_Native.Waiting Data)
    (fn value : Data) (a : Nat) (saved : c.frame.waiting = some wait)
    (request : wait.request = .child fn a [value]) :
    PV_THR2_Catch316Segment.select c = none := by
  simp [PV_THR2_Catch316Segment.select,saved,request]

/-- Propagate first-leaf divergence into the actual original saved caller.
Its saved request remains; this is not a successful restoration boundary. -/
theorem step18 (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    {E : Type} (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (x : Entry E) (valid : EntryValid x) (lower : x.parents ≠ []) :
    PV_THR2_IntrinsicState.step (machine C b K P H).carrier
      (machine C b K P H).control (machine C b K P H).programs H (at18 x H) = at19 x H := by
  let parent : Config := ⟨x.parent,x.parents,(pending x).store⟩
  exact PV_FN_THREAD_f6CompletionPropagation.intrinsic
    (machine C b K P H).carrier (machine C b K P H).control
    (machine C b K P H).programs H parent (pending x).frame x.wait
    (reply x H).world (x.events ++ (reply x H).events) x.suspended valid.2.2.1 lower
    (by rfl)

/-- A completed caller with an invalid lower return frame reaches an
interpretation gap. Both dynamic and aggregate-completion wrappers are included.
The arbitrary suffix is allowed by EntryValid; it is not row code. -/
theorem lower_gap {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (outer : Frame) (w : W) (es : List E) (stack : List Config)
    (done : c.frame.completed = some .div) (callers : c.callers = [outer])
    (waiting : outer.waiting = none) (ordinary : PV_THR2_Catch316Segment.select c = none) :
    PV_THR2_IntrinsicState.step B K P H ⟨⟨.running c,w,es⟩,stack⟩ =
      ⟨⟨.undefined none c.store,w,es⟩,stack⟩ := by
  simp [PV_THR2_IntrinsicState.step,ordinary,PV_THR2_Execution.step,
    PV_THR2_Dynamic.active,done,PV_THR2_GapCompletion.step,
    PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,callers,waiting]

#print axioms entry_div
#print axioms single_no_catch
#print axioms step18
#print axioms lower_gap
end PV_FN_THREAD_f6DivergenceBoundary
