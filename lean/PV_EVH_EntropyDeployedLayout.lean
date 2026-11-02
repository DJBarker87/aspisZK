import PV_EVH_EntropyInnerFrame
set_option autoImplicit false
namespace PV_EVH_EntropyDeployedLayout
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackRegions (Separate)
open PV_EVH_StackAdmission (HeapSeparate LiveSeparate)

/-- Offsets read from the hash-checked adopted da36d6aa artifact. The actual
reached-state interpretation is FRAME-CALL/V370, not a theorem about all State.
The stack base is symbolic: no unoccupied address is invented. -/
def original (owner sp : Nat) (w : State) : Slot :=
  PV_EVH_EntropySourceSlot.original owner sp w

def entered (owner sp : Nat) (w : State) : State :=
  PV_EVH_StackAdmission.enter (original owner sp w) (List.replicate 64 0) w

def field (owner sp : Nat) (w : State) : Slot :=
  PV_EVH_EntropyInnerFrame.fieldSlot owner (sp+64) (entered owner sp w)

def seed (owner sp : Nat) (w : State) : Slot :=
  PV_EVH_EntropyInnerFrame.seedSlot owner (sp+64) (sp+96) (entered owner sp w)

/-- The external FRAME-ENTRY obligation is outside the entire actual reserved
frame. It is not inferred from fresh keys or from source array values. -/
def OutsideFrame (sp address : Nat) : Prop := address < sp ∨ sp+232 ≤ address

theorem extents (owner sp : Nat) (w : State) :
    (original owner sp w).initialized = 64 ∧
    (field owner sp w).initialized = 32 ∧ (seed owner sp w).initialized = 32 :=
  ⟨rfl,rfl,rfl⟩

/-- Discharges the three independent numeric FRAME premises of delivered_halves. -/
theorem separation (owner sp : Nat) (w : State) :
    Separate (field owner sp w) (original owner sp w) ∧
    Separate (seed owner sp w) (original owner sp w) ∧
    Separate (seed owner sp w) (field owner sp w) := by
  change (sp+64+32 ≤ sp ∨ sp+64 ≤ sp+64) ∧
    (sp+96+32 ≤ sp ∨ sp+64 ≤ sp+96) ∧
    (sp+96+32 ≤ sp+64 ∨ sp+64+32 ≤ sp+96)
  omega

theorem outside_slots (owner sp address : Nat) (w : State)
    (h : OutsideFrame sp address) :
    PV_EVH_StackAdmission.Outside (original owner sp w) address ∧
    PV_EVH_StackAdmission.Outside (field owner sp w) address ∧
    PV_EVH_StackAdmission.Outside (seed owner sp w) address := by
  change (address < sp ∨ sp+64 ≤ address) ∧
    (address < sp+64 ∨ sp+64+32 ≤ address) ∧
    (address < sp+96 ∨ sp+96+32 ≤ address)
  unfold OutsideFrame at h
  omega

/-- All initialized source bytes are valid64-bit addresses once the actual
reserved frame has the runtime's valid nonwrapping extent. -/
theorem address_bounds (owner sp : Nat) (w : State)
    (h : sp+232 ≤ 2^64) (i : Nat) (hi : i < 32) :
    (original owner sp w).address+i < 2^64 ∧
    (original owner sp w).address+(32+i) < 2^64 ∧
    (field owner sp w).address+i < 2^64 ∧
    (seed owner sp w).address+i < 2^64 := by
  change sp+i < 2^64 ∧ sp+(32+i) < 2^64 ∧ sp+64+i < 2^64 ∧ sp+96+i < 2^64
  omega

/-- Derives every source-slot heap frame from the actual call-frame boundary.
That external boundary and HEAP-ENTRY coherence remain runtime obligations. -/
theorem heap_frames (owner sp : Nat) (w : State)
    (hh : ∀ b ∈ w.frame.runtime.heap, ∀ i, i < b.bytes.length →
      OutsideFrame sp (b.address+i)) :
    HeapSeparate (original owner sp w) w ∧
    HeapSeparate (field owner sp w) w ∧ HeapSeparate (seed owner sp w) w := by
  exact ⟨fun b hb i hi => (outside_slots owner sp _ w (hh b hb i hi)).1,
    fun b hb i hi => (outside_slots owner sp _ w (hh b hb i hi)).2.1,
    fun b hb i hi => (outside_slots owner sp _ w (hh b hb i hi)).2.2⟩

theorem live_frames (owner sp : Nat) (w : State)
    (hl : ∀ old ∈ w.frame.live, ∀ i, i < old.initialized →
      OutsideFrame sp (old.address+i)) :
    LiveSeparate (original owner sp w) w ∧
    LiveSeparate (field owner sp w) w ∧ LiveSeparate (seed owner sp w) w := by
  exact ⟨fun old ho i hi => (outside_slots owner sp _ w (hl old ho i hi)).1,
    fun old ho i hi => (outside_slots owner sp _ w (hl old ho i hi)).2.1,
    fun old ho i hi => (outside_slots owner sp _ w (hl old ho i hi)).2.2⟩

theorem original_admission (owner sp : Nat) (w : State)
    (hh : ∀ b ∈ w.frame.runtime.heap, ∀ i, i < b.bytes.length →
      OutsideFrame sp (b.address+i))
    (hl : ∀ old ∈ w.frame.live, ∀ i, i < old.initialized →
      OutsideFrame sp (old.address+i)) :
    PV_EVH_StackEntropyCoherence.Admission (original owner sp w) w :=
  PV_EVH_EntropySourceSlot.admission owner sp w
    (heap_frames owner sp w hh).1 (live_frames owner sp w hl).1

#print axioms extents
#print axioms separation
#print axioms outside_slots
#print axioms address_bounds
#print axioms heap_frames
#print axioms live_frames
#print axioms original_admission
end PV_EVH_EntropyDeployedLayout
