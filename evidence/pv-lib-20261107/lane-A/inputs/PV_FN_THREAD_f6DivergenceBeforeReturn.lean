import PV_FN_THREAD_f6DivergenceBoundary
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6DivergenceBeforeReturn
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces PV_FN_THREAD_f6DivergenceBoundary

/-- Compose the first native divergence with the original caller's completion
step. No instruction of the lower caller is executed. -/
theorem run19 {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (x : Entry E) (body : x.body = PV_THR2_F6.live) (valid : EntryValid x)
    (lower : x.parents ≠ []) (diverged : (reply x H).answer = .returned .div) :
    PV_FN_THREAD_f6Interfaces.run (machine C b K P H) x 19 = at19 x H := by
  unfold PV_FN_THREAD_f6Interfaces.run
  rw [show 19 = 18+1 from rfl,PV_THR2_IntrinsicComposition.advance_add]
  change PV_THR2_IntrinsicState.step (machine C b K P H).carrier
    (machine C b K P H).control (machine C b K P H).programs H
    (PV_FN_THREAD_f6Interfaces.run (machine C b K P H) x 18) = _
  rw [entry_div C b K P H x body diverged]
  exact step18 C b K P H x valid lower

def gap {E : Type} (x : Entry E)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data) :
    PV_THR2_IntrinsicState.State OWNER E :=
  ⟨⟨.undefined none (pending x).store,(reply x H).world,
    x.events ++ (reply x H).events⟩,x.suspended⟩

/-- Original f6 entry reaches a gap after an allowed first-leaf div answer and
an arbitrary lower suffix whose final frame has no saved request. EntryValid
constrains only the immediate caller, so this suffix is admissible there. -/
theorem run20 {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (x : Entry E) (callback : Data) (outer : Frame)
    (body : x.body = PV_THR2_F6.live) (valid : EntryValid x)
    (args : x.args = [callback]) (lower : x.parents = [outer])
    (outerWait : outer.waiting = none)
    (diverged : (reply x H).answer = .returned .div) :
    PV_FN_THREAD_f6Interfaces.run (machine C b K P H) x 20 = gap x H := by
  have nonempty : x.parents ≠ [] := by rw [lower]; intro h; cases h
  unfold PV_FN_THREAD_f6Interfaces.run
  rw [show 20 = 19+1 from rfl,PV_THR2_IntrinsicComposition.advance_add]
  change PV_THR2_IntrinsicState.step (machine C b K P H).carrier
    (machine C b K P H).control (machine C b K P H).programs H
    (PV_FN_THREAD_f6Interfaces.run (machine C b K P H) x 19) = _
  rw [run19 C b K P H x body valid nonempty diverged]
  rcases valid.2.2.2.2.1 with ⟨fn,request⟩
  have req : x.wait.request = .child fn x.activation [callback] := by rw [request,args]
  exact lower_gap (machine C b K P H).carrier (machine C b K P H).control
    (machine C b K P H).programs H _ outer (reply x H).world
    (x.events ++ (reply x H).events) x.suspended rfl lower outerWait
    (single_no_catch _ x.wait fn callback x.activation valid.2.2.1 req)

/-- A still-active f6 frame is distinct from the older immediate caller. -/
theorem active_not_returned {E : Type} (x : Entry E)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config)
    (status : q.current.status = .running c) (activation : c.frame.activation = x.activation)
    (older : x.parent.activation < x.activation) : ¬ Returned x q := by
  intro returned
  rcases returned with ⟨d,equal,frame,_,_⟩
  rw [status] at equal
  cases equal
  have same := congrArg Frame.activation frame
  change c.frame.activation = x.parent.activation at same
  omega

/-- The gap is INSIDE the existing BeforeReturn domain. No earlier successful
restoration is omitted: own prefixes0..16, the actual request17, div18 and
retained-waiting completion19 are checked separately by named certificates. -/
theorem before20 {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (x : Entry E) (body : x.body = PV_THR2_F6.live) (valid : EntryValid x)
    (lower : x.parents ≠ []) (diverged : (reply x H).answer = .returned .div) :
    BeforeReturn (machine C b K P H) x 20 := by
  intro m bound
  by_cases early : m ≤ 16
  · have act : ∃ c, (PV_FN_THREAD_f6Interfaces.run (machine C b K P H) x m).current.status =
        .running c ∧ c.frame.activation = x.activation := by
      unfold PV_FN_THREAD_f6Interfaces.run entry
      rw [body]
      exact PV_FN_THREAD_f6EarlyControl.activation
        (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier C)))
        K (PV_FN_THREAD_f6Reply121.programs P) H x.store x.activation
        (x.parent :: x.parents) b x.world x.events x.suspended m early
    rcases act with ⟨c,status,activation⟩
    exact active_not_returned x _ c status activation valid.2.1
  have options : m = 17 ∨ m = 18 ∨ m = 19 := by omega
  rcases options with h17 | h18 | h19
  · subst m
    have atRequest : PV_FN_THREAD_f6Interfaces.run (machine C b K P H) x 17 =
        ⟨⟨.running (pending x),x.world,x.events⟩,x.suspended⟩ := by
      unfold PV_FN_THREAD_f6Interfaces.run entry
      rw [body]
      exact PV_FN_THREAD_f6Entry.request (PV_THR2_RangeLiterals.carrier C) K
        (PV_FN_THREAD_f6Reply121.programs P) H x.store x.activation
        (x.parent :: x.parents) b x.world x.events x.suspended
    exact active_not_returned x _ _ (congrArg (fun q : PV_THR2_IntrinsicState.State OWNER E => q.current.status) atRequest) rfl valid.2.1
  · subst m
    exact active_not_returned x _ _
      (congrArg (fun q : PV_THR2_IntrinsicState.State OWNER E => q.current.status) (entry_div C b K P H x body diverged)) rfl valid.2.1
  · subst m
    rw [run19 C b K P H x body valid lower diverged]
    intro returned
    rcases returned with ⟨c,status,frame,_,_⟩
    cases status
    have waiting := congrArg Frame.waiting frame
    change x.parent.waiting = none at waiting
    rw [valid.2.2.1] at waiting
    cases waiting

/-- Checked obstruction to FullPost on this original-entry branch. Divergence
must not require interpreting arbitrary lower frames after the row has exited.
This is a model/contract boundary counterexample, not a Rust execution claim. -/
theorem not_full_post {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (x : Entry E) (callback : Data) (outer : Frame)
    (body : x.body = PV_THR2_F6.live) (valid : EntryValid x)
    (args : x.args = [callback]) (lower : x.parents = [outer])
    (outerWait : outer.waiting = none)
    (diverged : (reply x H).answer = .returned .div)
    (valuePost : Store Data → OWNER → Data → Prop) :
    ¬ FullPost (machine C b K P H) x valuePost := by
  intro post
  have nonempty : x.parents ≠ [] := by rw [lower]; intro h; cases h
  have safe := (post 20 (before20 C b K P H x body valid nonempty diverged)).1
  rw [run20 C b K P H x callback outer body valid args lower outerWait diverged] at safe
  exact safe

/-- The original Pre imposes no requirement on the lower suffix. Replacing it
by the final frame used in the counterexample preserves EVERY Pre conjunct. -/
theorem pre_suffix {E F Task : Type} (x : Entry E)
    (captures : PV_EVHB_OrderedFamiliesEntry.Captures F Task) (callback : Data)
    (outer : Frame) (pre : PV_FN_THREAD_f6.Pre x captures callback) :
    PV_FN_THREAD_f6.Pre {x with parents := [outer]} captures callback := by
  exact pre

/-- A concrete non-success world answer for the countermodel. It preserves
all OWNER/world state and emits no events; no success value is invented. -/
def divHandler {E : Type} (_ : PV_STX2_Native.Request Data) (w : OWNER) : Reply OWNER E Data :=
  ⟨.returned .div,w,[]⟩

/-- Every supplied original Pre instance admits a lower suffix for which its
Post is false on the allowed div branch. This exposes the prefix boundary
problem without assuming a future read, gap, coverage or successful endpoint.
It does not assert a defect in the Rust AtomicUsize constructor. -/
theorem counterexample_from_pre {E F Task : Type}
    (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (x : Entry E)
    (captures : PV_EVHB_OrderedFamiliesEntry.Captures F Task) (callback : Data)
    (pre : PV_FN_THREAD_f6.Pre x captures callback) :
    let outer : Frame := {activation := 0,remaining := []}
    let z := {x with parents := [outer]}
    PV_FN_THREAD_f6.Pre z captures callback ∧
      ¬ PV_FN_THREAD_f6.Post (machine C b K P divHandler) z := by
  intro outer z
  refine ⟨pre_suffix x captures callback outer pre,?_⟩
  unfold PV_FN_THREAD_f6.Post
  exact not_full_post C b K P divHandler z callback outer pre.1 pre.2.2.1
    pre.2.1 rfl rfl rfl _

#print axioms run19
#print axioms run20
#print axioms active_not_returned
#print axioms before20
#print axioms not_full_post
#print axioms pre_suffix
#print axioms counterexample_from_pre
end PV_FN_THREAD_f6DivergenceBeforeReturn
