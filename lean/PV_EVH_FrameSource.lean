import PV_EVH_FrameTransitions
import PV_EVH_NativeEntropyRejected
set_option autoImplicit false
noncomputable section
namespace PV_EVH_FrameSource
open PV_EVH_PhysicalFrame PV_EVH_FrameTransitions
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_NativeRawSelection (rawBase)
open PV_EVH_StackZero (State)

/-- Projection of a paired actual prefix, not a replacement definition of the
fixed ActualEntropyEntryPrefix domain. No arbitrary process memory is added:
physical bytes are the SAME source/native State.memory. The producer must
supply this view from its paired history, under binary-structural plus V370. -/
structure EntryView where
  state : State
  thread : Nat
  activation : Nat
  sp : Nat
  loadBias : Nat
  stackLimit : Nat
  retry : Fin 8
  iteration : Fin 16
  retryHistory : RetryPrefix retry.val (retry.val+1)
  answer : StackAnswer ⟨thread,activation,sp,232,stackLimit⟩

/-- Initializer PC, after mask/retry guards and before secret initialization.
Both pending and exhausted first-access answers are retained. -/
def rip (q : EntryView) : Nat := q.loadBias + 0x1457ef

def frame (q : EntryView) : Frame :=
  interpret q.thread q.activation q.sp q.stackLimit q.retry q.iteration .beforeInit q.answer

def physicalMemory (q : EntryView) : Nat → Nat := q.state.memory

def plan (q : EntryView) : Activation :=
  ⟨q.activation+9,q.sp+288+336*(q.retry.val+1),21160⟩

/-- Named spine only. Earlier client callers, signal frames and other threads
are retained by the enclosing producer; they are not claimed absent. -/
def activeSpine (q : EntryView) : List Activation :=
  plan q :: (frame q).activeFrames ++ [⟨q.activation,q.sp,232⟩]

theorem entry_consistent (q : EntryView) :
    (∀ a b, a ≠ b → Separate ((frame q).slotTable a) ((frame q).slotTable b)) ∧
    (frame q).activeFrames.length ≤ 8 ∧ (activeSpine q).length ≤ 10 := by
  have h := shape_consistent (frame q)
    (interpret_shape q.thread q.activation q.sp q.stackLimit q.retry q.iteration
      .beforeInit q.answer)
  refine ⟨h.1,h.2,?_⟩
  simp only [activeSpine,List.length_cons,List.length_append,List.length_singleton]
  omega

/-- Concrete source slot projection; identity remains the existing source
key, not a second owner model. Iteration lifetime pairs are frame metadata. -/
def sourceOriginal (q : EntryView) :=
  PV_EVH_EntropyDeployedLayout.original q.activation q.sp q.state

def sourceField (q : EntryView) :=
  PV_EVH_EntropyDeployedLayout.field q.activation q.sp q.state

def sourceSeed (q : EntryView) :=
  PV_EVH_EntropyDeployedLayout.seed q.activation q.sp q.state

def SameStorage (source : PV_EVH_StackZero.Slot) (physical : Slot) : Prop :=
  source.address = physical.address ∧ source.initialized = physical.bytes

theorem source_slots (q : EntryView) :
    SameStorage (sourceOriginal q) ((frame q).slotTable (.inner ⟨0,by omega⟩)) ∧
    SameStorage (sourceField q) ((frame q).slotTable (.inner ⟨1,by omega⟩)) ∧
    SameStorage (sourceSeed q) ((frame q).slotTable (.inner ⟨2,by omega⟩)) :=
  ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩

/-- FRAME's source-facing interface over the UNCHANGED actual domain. It does
not construct that domain, add a successful-prefix restriction, or assume
separation in a field. Exact mask/world association is an explicit structural
correspondence obligation of the paired-prefix producer, never OWNER. -/
structure Correspondence (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
    (ops : @ExternalFuns (types (rawBase base)))
    (ActualEntropyEntryPrefix : Type) where
  view : ActualEntropyEntryPrefix → EntryView
  sourceState : ActualEntropyEntryPrefix → State
  sourceMask : ActualEntropyEntryPrefix → Array U8 32#usize
  sourceRetry : ActualEntropyEntryPrefix → Usize
  sourceLimit : ActualEntropyEntryPrefix → Usize
  state_eq : ∀ q, (view q).state = sourceState q
  retry_eq : ∀ q, (sourceRetry q).val = (view q).iteration.val
  limit_eq : ∀ q, (sourceLimit q).val = 16
  mask_backing : ∀ q (i : Nat), i < 32 →
    (view q).state.memory ((view q).sp+304+i) =
      ((sourceMask q).val[i]!).val

/-- The exact reached expression at the original four-binder dictionary.
This is an expression index, NOT a supplied result or a success continuation. -/
def sourceBody (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
    (ops : @ExternalFuns (types (rawBase base)))
    (P : Type) (c : Correspondence base heap box ops P) (q : P) :=
  letI : ExternalTypes := types (rawBase base)
  letI : ExternalFuns := opsNative (rawBase base) heap box ops
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
    (c.sourceMask q) (c.sourceLimit q) (c.sourceRetry q)

/-- No extra separation premise: the concrete FRAME view derives it. This
conditional interface theorem is not a proof that the actual producer exists. -/
theorem correspondence_consistent (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
    (ops : @ExternalFuns (types (rawBase base)))
    (P : Type) (c : Correspondence base heap box ops P) (q : P) :
    (frame (c.view q)).activeFrames.length ≤ 8 ∧
    ∀ a b, a ≠ b → Separate ((frame (c.view q)).slotTable a)
      ((frame (c.view q)).slotTable b) := by
  have h := entry_consistent (c.view q)
  exact ⟨h.2.1,h.1⟩

/-- Joins the physical lifetime backedge with the EXISTING checked cleanup's
source-key freshness, retaining its original State and native delivery. -/
theorem rejected_lifetimes (base : ExternalTypes) :
    letI : ExternalTypes := types (rawBase base)
    ∀ (q : EntryView) (d : PV_EVH_StackEntropyFill.Delivery)
      (guard : q.iteration.val+1 < 16),
      Shape (nextIteration (frame q) guard) ∧
      (sourceOriginal q).key.identity <
        (PV_EVH_EntropyDeployedLayout.original q.activation q.sp
          (PV_EVH_EntropyRejectDelivery.completed q.activation q.sp d q.state)).key.identity := by
  letI : ExternalTypes := types (rawBase base)
  intro q d guard
  exact ⟨(iteration_preserves (frame q)
    (interpret_shape q.thread q.activation q.sp q.stackLimit q.retry q.iteration
      .beforeInit q.answer) guard).1,
    PV_EVH_EntropyRejectDelivery.next_original_fresh q.activation q.sp d q.state⟩

/-- Exhaustion keeps the actual fault and the post-answer world/events, not an
entropy error or fabricated initialized buffer. No []-event convention. -/
structure ResourceReply (request : Request) where
  before : State
  after : State
  events : List PV_RJ4IDB.NativeEvent
  answer : StackAnswer request

def resourceOutcome (request : Request) (r : ResourceReply request) :
    Option (PV_EVH_Runtime.Outcome Unit) :=
  match r.answer with
  | .pending => none
  | .granted _ => some (.returned (.ok ()))
  | .exhausted fault => some (.fault fault)

theorem exhaustion_retained (request : Request) (r : ResourceReply request)
    (fault : PV_EVH_Runtime.Fault) (h : r.answer = .exhausted fault) :
    resourceOutcome request r = some (.fault fault) := by
  simp only [resourceOutcome,h]

#print axioms entry_consistent
#print axioms source_slots
#print axioms correspondence_consistent
#print axioms rejected_lifetimes
#print axioms exhaustion_retained
end PV_EVH_FrameSource
