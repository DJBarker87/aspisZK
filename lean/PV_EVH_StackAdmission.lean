import PV_EVH_StackCleanup
set_option autoImplicit false
namespace PV_EVH_StackAdmission
open PV_EVH_StackZero (Slot State)
open PV_EVH_HeapOwnership (Key)
open PV_RJ4IDB (Bytes)

def Outside (slot : Slot) (address : Nat) : Prop :=
  address < slot.address ∨ slot.address + slot.initialized ≤ address

/-- Initialization writes exactly the original stack region. Extensional bytes
never choose an allocation or a replacement owner. -/
def write (slot : Slot) (bytes : Bytes) (w : State) : State :=
  {w with memory := fun address =>
    if slot.address ≤ address ∧ address < slot.address+slot.initialized
    then (bytes[address-slot.address]?.getD 0).toNat else w.memory address}

/-- A ghost lifetime admission accompanying the source stack initializer.
Freshness, address separation and actual source-frame association are proof
obligations; this does not add a fictitious Rust allocation or failure branch. -/
def enter (slot : Slot) (bytes : Bytes) (w : State) : State :=
  let f : PV_EVH_StackZero.Frame :=
    ⟨w.frame.runtime,slot :: w.frame.live,w.frame.retired⟩
  {write slot bytes w with frame := f}

def HeapCoherent (w : State) : Prop :=
  ∀ b ∈ w.frame.runtime.heap, ∀ i, i < b.bytes.length →
    w.memory (b.address+i) = (b.bytes[i]?.getD 0).toNat

def HeapSeparate (slot : Slot) (w : State) : Prop :=
  ∀ b ∈ w.frame.runtime.heap, ∀ i, i < b.bytes.length → Outside slot (b.address+i)

def LiveSeparate (slot : Slot) (w : State) : Prop :=
  ∀ old ∈ w.frame.live, ∀ i, i < old.initialized → Outside slot (old.address+i)

theorem write_inside (slot : Slot) (bytes : Bytes) (w : State)
    (i : Nat) (hi : i < slot.initialized) :
    (write slot bytes w).memory (slot.address+i) = (bytes[i]?.getD 0).toNat := by
  simp only [write]
  rw [if_pos (by omega),Nat.add_sub_cancel_left]

theorem write_outside (slot : Slot) (bytes : Bytes) (w : State)
    (address : Nat) (h : Outside slot address) :
    (write slot bytes w).memory address = w.memory address := by
  simp only [write]
  rw [if_neg (by unfold Outside at h; omega)]

theorem enter_lookup (slot : Slot) (bytes : Bytes) (w : State) :
    (enter slot bytes w).frame.live.find?
      (PV_EVH_StackCleanup.sameKey slot.key) = some slot := by
  simp only [enter,List.find?_cons,PV_EVH_StackCleanup.sameKey,beq_self_eq_true,
    Bool.and_self,if_true]

theorem enter_heap (slot : Slot) (bytes : Bytes) (w : State)
    (hc : HeapCoherent w) (hs : HeapSeparate slot w) :
    HeapCoherent (enter slot bytes w) := by
  intro b hb i hi
  exact (write_outside slot bytes w (b.address+i) (hs b hb i hi)).trans (hc b hb i hi)

theorem enter_live (slot old : Slot) (bytes : Bytes) (w : State)
    (hs : LiveSeparate slot w) (ho : old ∈ w.frame.live)
    (i : Nat) (hi : i < old.initialized) :
    (enter slot bytes w).memory (old.address+i) = w.memory (old.address+i) :=
  write_outside slot bytes w (old.address+i) (hs old ho i hi)

theorem drop_heap (slot : Slot) (w : State)
    (hc : HeapCoherent w) (hs : HeapSeparate slot w) :
    HeapCoherent (PV_EVH_StackZero.drop slot w) := by
  intro b hb i hi
  rw [PV_EVH_StackZero.dropped_runtime] at hb
  exact (PV_EVH_StackZero.outside_preserved slot w (b.address+i) (hs b hb i hi)).trans
    (hc b hb i hi)

theorem enter_runtime (slot : Slot) (bytes : Bytes) (w : State) :
    (enter slot bytes w).frame.runtime = w.frame.runtime := rfl

#print axioms write_inside
#print axioms write_outside
#print axioms enter_lookup
#print axioms enter_heap
#print axioms enter_live
#print axioms drop_heap
#print axioms enter_runtime
end PV_EVH_StackAdmission
