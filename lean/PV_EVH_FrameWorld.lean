import PV_EVH_FrameSource
set_option autoImplicit false
noncomputable section
namespace PV_EVH_FrameWorld
open PV_EVH_PhysicalFrame PV_EVH_FrameTransitions PV_EVH_FrameSource
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_NativeRawSelection (rawBase)

/-- Resource observation only: granting a stack request does not run the
secret initializer. Pending, fault and post-answer world are distinct. -/
structure ResourceRun where
  frame : Frame
  state : PV_EVH_StackZero.State
  events : List PV_RJ4IDB.NativeEvent
  outcome : Option (PV_EVH_Runtime.Outcome Unit)

/-- The before equality couples this answer to this prefix. All continuation
work consumes r.after. No pre-answer VMA or resource-adequacy premise. -/
def resolve (q : EntryView) (r : ResourceReply (frame q).request)
    (_samePrefix : r.before = q.state) : ResourceRun :=
  ⟨match r.answer with
    | .exhausted _ => {frame q with phase := .stopped}
    | _ => frame q,
   r.after,r.events,resourceOutcome (frame q).request r⟩

theorem answer_world (q : EntryView) (r : ResourceReply (frame q).request)
    (samePrefix : r.before = q.state) :
    (resolve q r samePrefix).state = r.after ∧
    (resolve q r samePrefix).events = r.events := ⟨rfl,rfl⟩

theorem answer_preserves (q : EntryView) (r : ResourceReply (frame q).request)
    (samePrefix : r.before = q.state) : Shape (resolve q r samePrefix).frame := by
  have h := interpret_shape q.thread q.activation q.sp q.stackLimit q.retry
    q.iteration .beforeInit q.answer
  cases ha : r.answer <;> simpa only [resolve,ha,Shape] using h

theorem answer_fault (q : EntryView) (r : ResourceReply (frame q).request)
    (samePrefix : r.before = q.state) (fault : PV_EVH_Runtime.Fault)
    (h : r.answer = .exhausted fault) :
    (resolve q r samePrefix).outcome = some (.fault fault) ∧
    (resolve q r samePrefix).frame.phase = .stopped ∧
    (resolve q r samePrefix).state = r.after ∧
    (resolve q r samePrefix).events = r.events := by
  simp only [resolve,resourceOutcome,h]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Advance to the next initializer using the EXISTING rejected cleanup's
post-state. A fresh pending resource answer avoids promising future accesses.
No numeric address, old memory, or original source key is replaced by a fixture. -/
def nextEntry (base : ExternalTypes) :
    letI : ExternalTypes := types (rawBase base)
    (q : EntryView) → PV_EVH_StackEntropyFill.Delivery →
      (guard : q.iteration.val+1 < 16) → EntryView :=
  letI : ExternalTypes := types (rawBase base)
  fun q d guard =>
    {q with
      state := PV_EVH_EntropyRejectDelivery.completed q.activation q.sp d q.state
      iteration := ⟨q.iteration.val+1,guard⟩
      answer := .pending}

theorem next_entry_preserves (base : ExternalTypes) :
    letI : ExternalTypes := types (rawBase base)
    ∀ (q : EntryView) (d : PV_EVH_StackEntropyFill.Delivery)
      (guard : q.iteration.val+1 < 16),
      (frame (nextEntry base q d guard)).activeFrames = (frame q).activeFrames ∧
      (∀ id, ((frame (nextEntry base q d guard)).slotTable id).address =
        ((frame q).slotTable id).address) ∧
      (sourceOriginal q).key.identity < (sourceOriginal (nextEntry base q d guard)).key.identity ∧
      (∀ a b, a ≠ b → Separate ((frame (nextEntry base q d guard)).slotTable a)
        ((frame (nextEntry base q d guard)).slotTable b)) := by
  letI : ExternalTypes := types (rawBase base)
  intro q d guard
  refine ⟨rfl,?_,PV_EVH_EntropyRejectDelivery.next_original_fresh
    q.activation q.sp d q.state,(entry_consistent (nextEntry base q d guard)).1⟩
  intro id
  cases id <;> rfl

/-- Basic interface consistency is simultaneous for the next loop entry and
both inlined callback edges. This theorem changes no native trace selector. -/
theorem preserved_spine (q : EntryView) (guard : q.iteration.val+1 < 16)
    (entered : Nat) :
    (∀ a b, a ≠ b → Separate ((nextIteration (frame q) guard).slotTable a)
      ((nextIteration (frame q) guard).slotTable b)) ∧
    (nextIteration (frame q) guard).activeFrames.length ≤ 8 ∧
    Shape (callbackReturn (callbackCall ⟨frame q,entered,.ready⟩)).frame := by
  have hs := interpret_shape q.thread q.activation q.sp q.stackLimit q.retry
    q.iteration .beforeInit q.answer
  have hi := iteration_preserves (frame q) hs guard
  have hc := shape_consistent _ hi.1
  exact ⟨hc.1,hc.2,(callback_preserves ⟨frame q,entered,.ready⟩ hs).1⟩

#print axioms answer_world
#print axioms answer_preserves
#print axioms answer_fault
#print axioms next_entry_preserves
#print axioms preserved_spine
end PV_EVH_FrameWorld
