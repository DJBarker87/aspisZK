import PV_EVH_ZeroAddressBridge
set_option autoImplicit false
namespace PV_EVH_StackZero
open PV_EVH_Runtime PV_EVH_HeapOwnership
open PV_RJ4IDB (Bytes NativeEvent)

/-- A stack slot is separate from allocator-owned blocks. The source/native
association must establish the original exclusive slot and initialized extent. -/
structure Slot where
  key : Key
  address : Nat
  initialized : Nat

structure Frame where
  runtime : PV_EVH_Runtime.State
  live : List Slot
  retired : List Slot

abbrev State := PV_EVH_DeployedZeroWorld.World Frame

/-- Ending a lifetime retains its post-cleanup physical memory and its slot.
It does not assert allocator clearing or erase retired memory from L3. -/
def retire (slot : Slot) (w : State) : State :=
  {w with frame := {w.frame with
    live := w.frame.live.filter (fun s => s.key != slot.key)
    retired := slot :: w.frame.retired}
    drops := w.drops+1}

def drop (slot : Slot) (w : State) : State :=
  retire slot (PV_EVH_DeployedZeroCursor.run
    (slot.address+slot.initialized) slot.initialized slot.address w)

/-- Physical address-bearing observations, not a claim that cleanup is silent.
The text here is the mathematical event serialization, not Rust fmt semantics. -/
def nativeEvent : PV_EVH_DeployedZeroWorld.Event → NativeEvent
  | .volatileWrite address value =>
    .side (PV_EVH_World.ascii "zeroize.volatileWrite")
      (PV_EVH_World.ascii (toString address ++ ":" ++ toString value))
  | .asmReadBarrier address =>
    .side (PV_EVH_World.ascii "zeroize.asmReadBarrier")
      (PV_EVH_World.ascii (toString address))

def emitted (slot : Slot) : List NativeEvent :=
  (PV_EVH_DeployedZeroTrace.trace slot.address slot.initialized).map nativeEvent

def Cleared (slot : Slot) (w : State) : Prop :=
  ∀ i, i < slot.initialized → w.memory (slot.address+i) = 0

theorem dropped_cleared (slot : Slot) (w : State) : Cleared slot (drop slot w) := by
  intro i hi
  exact PV_EVH_ZeroAddressBridge.cursor_overwrites slot.address slot.initialized i w hi

theorem dropped_history (slot : Slot) (w : State) :
    (drop slot w).history = w.history ++
      (PV_EVH_ZeroizeArray.events slot.key 0 slot.initialized).map
        (PV_EVH_ZeroAddressBridge.physical slot.address) :=
  PV_EVH_ZeroAddressBridge.cursor_history slot.key slot.address slot.initialized w

theorem dropped_runtime (slot : Slot) (w : State) :
    (drop slot w).frame.runtime = w.frame.runtime := by
  have hf := (PV_EVH_DeployedZeroWorld.frame slot.address slot.initialized w).1
  change (PV_EVH_DeployedZeroCursor.run _ _ _ w).frame.runtime = _
  rw [PV_EVH_DeployedZeroCursor.source,hf]

theorem retired_after_drop (slot : Slot) (w : State) :
    (drop slot w).frame.retired = slot :: w.frame.retired := by
  have hf := (PV_EVH_DeployedZeroWorld.frame slot.address slot.initialized w).1
  change slot :: (PV_EVH_DeployedZeroCursor.run _ _ _ w).frame.retired = _
  rw [PV_EVH_DeployedZeroCursor.source,hf]

theorem outside_preserved (slot : Slot) (w : State) (address : Nat)
    (h : address < slot.address ∨ slot.address+slot.initialized ≤ address) :
    (drop slot w).memory address = w.memory address := by
  change (PV_EVH_DeployedZeroCursor.run _ _ _ w).memory address = _
  rw [PV_EVH_DeployedZeroCursor.source]
  exact PV_EVH_DeployedZeroWorld.outside slot.address slot.initialized w address h

#print axioms dropped_cleared
#print axioms dropped_history
#print axioms dropped_runtime
#print axioms retired_after_drop
#print axioms outside_preserved
end PV_EVH_StackZero
