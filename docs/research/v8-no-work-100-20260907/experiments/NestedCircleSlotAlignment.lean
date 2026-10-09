import NestedCircleTermination

/-! Local named-slot/source alignment without importing a coordinate router.
Live slots are selected before answers and never reuse a recorded key. The
log stores the actual chronological answer, in reverse chronological order.
Halted updates are ghost padding and leave both control and log unchanged.
No measure, oracle freshness, or finite-coordinate equivalence is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.NestedCircleSlotAlignment
noncomputable section
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder
open AspisV8.NestedCircleRouting
open AspisV8.NestedCircleStatusRefinement
open AspisV8.NestedCircleRunRefinement
open AspisV8.NestedCircleTermination

def slotOrdinal : Slot → Nat
  | .inl (inner, word) => 4 * inner.val + word.val
  | .inr (outer, inner, word) => 12 + 12 * outer.val + 4 * inner.val + word.val

def SlotShape (state : State) (slot : Slot) : Prop :=
  match state with
  | .first inner pending =>
      ∃ word : Fin 4, slot = .inl (inner, word) ∧ word.val = pending.length
  | .second _ outer inner pending =>
      ∃ word : Fin 4, slot = .inr (outer, inner, word) ∧ word.val = pending.length
  | _ => False

theorem preferred_shape (state : State) (slot : Slot)
    (picked : preferredSlot state = some slot) : SlotShape state slot := by
  cases state with
  | first inner pending =>
      by_cases short : pending.length < 4
      · simp only [preferredSlot, dif_pos short, Option.some.injEq] at picked
        exact ⟨⟨pending.length, short⟩, picked.symm, rfl⟩
      · simp [preferredSlot, short] at picked
  | second point outer inner pending =>
      by_cases short : pending.length < 4
      · simp only [preferredSlot, dif_pos short, Option.some.injEq] at picked
        exact ⟨⟨pending.length, short⟩, picked.symm, rfl⟩
      · simp [preferredSlot, short] at picked
  | accepted first second => simp [preferredSlot] at picked
  | aborted reason => simp [preferredSlot] at picked

theorem preferred_some_live (state : State) (slot : Slot)
    (picked : preferredSlot state = some slot) : ¬Halted state := by
  cases state <;> simp_all [preferredSlot, Halted]

theorem live_preferred_exists (state : State) (ready : Ready state)
    (live : ¬Halted state) : ∃ slot, preferredSlot state = some slot := by
  cases state with
  | first inner pending =>
      change ordinaryStatus pending = .needMore at ready
      have short := ordinary_needMore_short pending ready
      exact ⟨.inl (inner, ⟨pending.length, short⟩), by simp [preferredSlot, short]⟩
  | second point outer inner pending =>
      change ordinaryStatus pending = .needMore at ready
      have short := ordinary_needMore_short pending ready
      exact ⟨.inr (outer, inner, ⟨pending.length, short⟩), by simp [preferredSlot, short]⟩
  | accepted first second => exact False.elim (live True.intro)
  | aborted reason => exact False.elim (live True.intro)

/-- The requested cell is the exact frontier of the previously proved
source-read budget, not an arbitrary injective relabeling supplied by a caller. -/
theorem preferred_budget_identity (state : State) (slot : Slot)
    (picked : preferredSlot state = some slot) : slotOrdinal slot + readBudget state = 48 := by
  have shape := preferred_shape state slot picked
  cases state with
  | first inner pending =>
      obtain ⟨word, rfl, wordEq⟩ := shape
      have innerBound := inner.isLt
      have wordBound := word.isLt
      simp only [slotOrdinal, readBudget]
      omega
  | second point outer inner pending =>
      obtain ⟨word, rfl, wordEq⟩ := shape
      have outerBound := outer.isLt
      have innerBound := inner.isLt
      have wordBound := word.isLt
      simp only [slotOrdinal, readBudget]
      omega
  | accepted first second => exact False.elim shape
  | aborted reason => exact False.elim shape

abbrev ReadLog := List (Slot × Digest256)

/-- Latest entry first; equality is tested only on the finite slot key. -/
def observed (history : ReadLog) (slot : Slot) : Option Digest256 :=
  match history with
  | [] => none
  | (key, answer) :: rest => if key = slot then some answer else observed rest slot

def Before (state : State) (history : ReadLog) : Prop :=
  ∀ entry ∈ history, slotOrdinal entry.1 + readBudget state < 48

structure LoggedState where
  control : State
  history : ReadLog

def Good (frame : LoggedState) : Prop :=
  Ready frame.control ∧ Before frame.control frame.history ∧ (frame.history.map Prod.fst).Nodup

/-- Destination is computed from the prior controller state. Only the
new history entry depends on the newly received answer. -/
def loggedStep (circleMap : SecureCircleParameterMap) (frame : LoggedState)
    (answer : Digest256) : LoggedState :=
  { control := afterAnswer circleMap frame.control answer
    history := match preferredSlot frame.control with
      | some slot => (slot, answer) :: frame.history
      | none => frame.history }

def loggedInitial : LoggedState := ⟨initial, []⟩

def loggedRun (circleMap : SecureCircleParameterMap) (frame : LoggedState)
    (tape : List Digest256) : LoggedState := tape.foldl (loggedStep circleMap) frame

theorem preferred_unrecorded (state : State) (history : ReadLog) (slot : Slot)
    (before : Before state history) (picked : preferredSlot state = some slot) :
    slot ∉ history.map Prod.fst := by
  have frontier := preferred_budget_identity state slot picked
  intro member
  obtain ⟨entry, entryMem, keyEq⟩ := List.mem_map.mp member
  have earlier := before entry entryMem
  rw [keyEq] at earlier
  omega

theorem observed_none_of_unrecorded (history : ReadLog) (slot : Slot)
    (fresh : slot ∉ history.map Prod.fst) : observed history slot = none := by
  induction history with
  | nil => rfl
  | cons entry rest ih =>
      have keyNe : entry.1 ≠ slot := by
        intro equal
        apply fresh
        simp [equal]
      have tailFresh : slot ∉ rest.map Prod.fst := by
        intro member
        apply fresh
        simp [member]
      cases entry with
      | mk key answer =>
          simp only [observed, if_neg keyNe]
          exact ih tailFresh

/-- One actual answer is stored under the already selected slot. -/
theorem loggedStep_observed (circleMap : SecureCircleParameterMap)
    (frame : LoggedState) (slot : Slot) (answer : Digest256)
    (picked : preferredSlot frame.control = some slot) :
    observed (loggedStep circleMap frame answer).history slot = some answer := by
  simp [loggedStep, picked, observed]

theorem loggedStep_good (circleMap : SecureCircleParameterMap)
    (frame : LoggedState) (answer : Digest256) (good : Good frame) :
    Good (loggedStep circleMap frame answer) := by
  obtain ⟨ready, before, nodup⟩ := good
  have nextReady := afterAnswer_ready circleMap frame.control answer
  cases picked : preferredSlot frame.control with
  | none =>
      have halted : Halted frame.control := by
        by_contra live
        obtain ⟨slot, exists⟩ := live_preferred_exists frame.control ready live
        rw [picked] at exists
        contradiction
      have unchanged := halted_afterAnswer circleMap frame.control answer halted
      simpa [Good, loggedStep, picked, unchanged] using And.intro ready (And.intro before nodup)
  | some slot =>
      have live := preferred_some_live frame.control slot picked
      have decrease := answer_budget_decreases circleMap frame.control answer ready live
      have frontier := preferred_budget_identity frame.control slot picked
      have fresh := preferred_unrecorded frame.control frame.history slot before picked
      refine ⟨nextReady, ?_, ?_⟩
      · change Before (afterAnswer circleMap frame.control answer)
          (match preferredSlot frame.control with
           | some key => (key, answer) :: frame.history
           | none => frame.history)
        rw [picked]
        intro entry member
        simp only [List.mem_cons] at member
        rcases member with rfl | old
        · change slotOrdinal slot + readBudget (afterAnswer circleMap frame.control answer) < 48
          omega
        · have earlier := before entry old
          omega
      · simpa [loggedStep, picked] using List.nodup_cons.mpr (And.intro fresh nodup)

theorem loggedInitial_good : Good loggedInitial := by
  refine ⟨rfl, ?_, ?_⟩
  · intro entry member
    simp [loggedInitial] at member
  · simp [loggedInitial]

theorem loggedRun_good (circleMap : SecureCircleParameterMap) (frame : LoggedState)
    (tape : List Digest256) (good : Good frame) : Good (loggedRun circleMap frame tape) := by
  induction tape generalizing frame with
  | nil => exact good
  | cons answer unread ih =>
      simpa [loggedRun] using ih (loggedStep circleMap frame answer)
        (loggedStep_good circleMap frame answer good)

/-- The instrumented log cannot alter the actual controller state. -/
theorem loggedRun_control (circleMap : SecureCircleParameterMap)
    (frame : LoggedState) (tape : List Digest256) :
    (loggedRun circleMap frame tape).control =
      NestedCircleRunRefinement.run circleMap frame.control tape := by
  induction tape generalizing frame with
  | nil => rfl
  | cons answer unread ih =>
      simpa [loggedRun, NestedCircleRunRefinement.run, loggedStep] using
        ih (loggedStep circleMap frame answer)

/-- At any actual chronological prefix, a live next slot is fixed before
ALL possible next answers; it is unfilled and records precisely that answer. -/
theorem meaningful_next (circleMap : SecureCircleParameterMap) (prefix : List Digest256)
    (live : ¬Halted (loggedRun circleMap loggedInitial prefix).control) :
    ∃ slot,
      preferredSlot (loggedRun circleMap loggedInitial prefix).control = some slot ∧
      SlotShape (loggedRun circleMap loggedInitial prefix).control slot ∧
      observed (loggedRun circleMap loggedInitial prefix).history slot = none ∧
      ∀ answer, observed
        (loggedStep circleMap (loggedRun circleMap loggedInitial prefix) answer).history slot =
          some answer := by
  have good := loggedRun_good circleMap loggedInitial prefix loggedInitial_good
  obtain ⟨slot, picked⟩ := live_preferred_exists _ good.1 live
  have fresh := preferred_unrecorded _ _ slot good.2.1 picked
  exact ⟨slot, picked, preferred_shape _ slot picked,
    observed_none_of_unrecorded _ slot fresh,
    fun answer => loggedStep_observed circleMap _ slot answer picked⟩

/-- A post-halt fallback fill cannot change control or the meaningful read
log. Any external router filling a coordinate then is ghost padding. -/
theorem loggedStep_halted (circleMap : SecureCircleParameterMap)
    (frame : LoggedState) (answer : Digest256) (halted : Halted frame.control) :
    loggedStep circleMap frame answer = frame := by
  cases frame with
  | mk state history =>
      cases state with
      | first inner pending => exact False.elim halted
      | second point outer inner pending => exact False.elim halted
      | accepted first second => rfl
      | aborted reason => rfl

theorem loggedRun_halted (circleMap : SecureCircleParameterMap)
    (frame : LoggedState) (padding : List Digest256) (halted : Halted frame.control) :
    loggedRun circleMap frame padding = frame := by
  induction padding with
  | nil => rfl
  | cons answer rest ih =>
      simpa [loggedRun, loggedStep_halted circleMap frame answer halted] using ih

#print axioms preferred_shape
#print axioms preferred_some_live
#print axioms live_preferred_exists
#print axioms preferred_budget_identity
#print axioms preferred_unrecorded
#print axioms observed_none_of_unrecorded
#print axioms loggedStep_observed
#print axioms loggedStep_good
#print axioms loggedInitial_good
#print axioms loggedRun_good
#print axioms loggedRun_control
#print axioms meaningful_next
#print axioms loggedStep_halted
#print axioms loggedRun_halted
end
end AspisV8.NestedCircleSlotAlignment
