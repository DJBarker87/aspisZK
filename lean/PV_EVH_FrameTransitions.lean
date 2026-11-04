import PV_EVH_PhysicalFrame
set_option autoImplicit false
namespace PV_EVH_FrameTransitions
open PV_EVH_PhysicalFrame
/-! D585 FRAME only. Binary-structural (adopted binary), plus V370.
The relation follows the named retry/callback/entropy spine; it is not a
small-step semantics for all x86 instructions or the complete client. -/

/-- Includes k=8's terminal guard frame, which never enters entropy. -/
inductive RetryPrefix : Nat → Nat → Prop where
  | entry : RetryPrefix 0 1
  | rejected {k frames : Nat} : RetryPrefix k frames → k < 8 →
      RetryPrefix (k+1) (frames+1)

theorem retry_prefix_shape {k frames : Nat} (h : RetryPrefix k frames) :
    frames = k+1 ∧ k ≤ 8 := by
  induction h with
  | entry => omega
  | rejected h hk ih => omega

theorem reached_entropy_depth {k frames : Nat} (h : RetryPrefix k frames)
    (guard : k < 8) : frames ≤ 8 := by
  have hs := retry_prefix_shape h
  omega

theorem cap_check_depth {frames : Nat} (h : RetryPrefix 8 frames) :
    frames = 9 := (retry_prefix_shape h).1

/-- Only layout equalities, never non-overlap, writable memory, heap exclusion
or source reachability. Those cannot be hidden in this consistency predicate. -/
def Shape (f : Frame) : Prop :=
  f.slotTable = table f.sp f.activation f.iteration.val ∧
  f.offsets = offset ∧
  f.lifetimes = (fun id => (table f.sp f.activation f.iteration.val id).lifetime) ∧
  f.activeFrames = retryChain f.sp f.activation (f.retry.val+1)

theorem interpret_shape (thread activation sp stackLimit : Nat) (retry : Fin 8)
    (iteration : Fin 16) (phase : Phase)
    (answer : StackAnswer ⟨thread,activation,sp,232,stackLimit⟩) :
    Shape (interpret thread activation sp stackLimit retry iteration phase answer) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem shape_consistent (f : Frame) (h : Shape f) :
    (∀ a b, a ≠ b → Separate (f.slotTable a) (f.slotTable b)) ∧
    f.activeFrames.length ≤ 8 := by
  constructor
  · intro a b hab
    rw [h.1]
    exact table_separate f.sp f.activation f.iteration.val a b hab
  · rw [h.2.2.2,chain_length]
    exact Nat.succ_le_of_lt f.retry.isLt

/-- A backedge keeps the activation/stack and replaces local source lifetimes.
It does not erase staging, registers, retired bytes or any native events. -/
def nextIteration (f : Frame) (guard : f.iteration.val+1 < 16) : Frame :=
  {f with iteration := ⟨f.iteration.val+1,guard⟩, phase := .beforeInit,
    slotTable := table f.sp f.activation (f.iteration.val+1),
    lifetimes := fun id => (table f.sp f.activation (f.iteration.val+1) id).lifetime}

theorem iteration_preserves (f : Frame) (h : Shape f)
    (guard : f.iteration.val+1 < 16) :
    Shape (nextIteration f guard) ∧
    (nextIteration f guard).activeFrames = f.activeFrames ∧
    (nextIteration f guard).sp = f.sp :=
  ⟨⟨rfl,h.2.1,rfl,h.2.2.2⟩,rfl,rfl⟩

theorem iteration_fresh (f : Frame) (guard : f.iteration.val+1 < 16)
    (h : Shape f) (i : Fin 6) :
    ((nextIteration f guard).slotTable (.inner i)).address =
      (f.slotTable (.inner i)).address ∧
    ((nextIteration f guard).slotTable (.inner i)).lifetime ≠
      (f.slotTable (.inner i)).lifetime := by
  rw [h.1]
  constructor
  · rfl
  · intro heq
    have he := congrArg Lifetime.iteration heq
    change f.iteration.val+1 = f.iteration.val at he
    omega

inductive CallbackPhase where
  | ready | entered | returned
  deriving DecidableEq

structure CallbackCursor where
  frame : Frame
  entered : Nat
  phase : CallbackPhase

/-- The supplied callback is inlined at 0x5c9bb..0x5ca02. No push of a
fictitious callback activation. This models its stack effect only. -/
def callbackCall (c : CallbackCursor) : CallbackCursor :=
  {c with phase := .entered}

def callbackReturn (c : CallbackCursor) : CallbackCursor :=
  {c with entered := c.entered+1, phase := .returned}

theorem callback_preserves (c : CallbackCursor) (h : Shape c.frame) :
    Shape (callbackReturn (callbackCall c)).frame ∧
    (callbackReturn (callbackCall c)).frame = c.frame ∧
    (callbackReturn (callbackCall c)).entered = c.entered+1 :=
  ⟨h,rfl,rfl⟩

/-- Fixed public displacement; plan and entropy are separate activations. -/
theorem spine_displacement (k : Nat) (hk : k < 8) :
    336*(k+1)+288 ≤ 2976 ∧ 21208+336*(k+1)+288 ≤ 24184 := by omega

/-- Geometry including every retry reservation, not just secret slots. -/
theorem chain_frames_separate (sp activation i j : Nat) (hij : i < j) :
    sp+288+336*i+264 ≤ sp+288+336*j := by omega

theorem corrected_caller (sp c : Nat) (h : sp+288 = c) :
    c+16 = sp+304 ∧ c+64 = sp+352 ∧ c+64+97 = sp+449 ∧
    c+64+97 ≤ c+264 := by omega

inductive Access where
  | waiting | initialize | fault
  deriving DecidableEq

def access (request : Request) : StackAnswer request → Access
  | .pending => .waiting
  | .granted _ => .initialize
  | .exhausted _ => .fault

theorem exhaustion_no_initializer (request : Request) (fault : PV_EVH_Runtime.Fault) :
    access request (.exhausted fault) ≠ .initialize := by
  intro h; cases h

theorem pending_no_initializer (request : Request) :
    access request .pending ≠ .initialize := by
  intro h; cases h

#print axioms retry_prefix_shape
#print axioms reached_entropy_depth
#print axioms cap_check_depth
#print axioms interpret_shape
#print axioms shape_consistent
#print axioms iteration_preserves
#print axioms iteration_fresh
#print axioms callback_preserves
#print axioms spine_displacement
#print axioms chain_frames_separate
#print axioms corrected_caller
#print axioms exhaustion_no_initializer
#print axioms pending_no_initializer
end PV_EVH_FrameTransitions
