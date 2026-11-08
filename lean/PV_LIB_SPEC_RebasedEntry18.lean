import PV_LIB_SPEC_RebasedCaptures18
import PV_LIB_SPEC_EntryPre14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_RebasedEntry18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_AllocationImages
local instance : DecidableEq Address := Classical.decEq _
def slot : PV_LIB_SPEC_TlsBindings13.Slot := ⟨⟨0,20,[]⟩,65520⟩
def store : Store Data :=
  PV_STX2_Store.write PV_LIB_SPEC_ConcreteEntry.store slot.source (some (.boolean false))

/-- Only the physical components of the initial owner change. The native
Thread allocation is live48/8 with sparse bytes; stack/TLS and counter are
static memory, never fabricated source OWNER registrations. -/
def tlsState : OWNER :=
  let old := PV_LIB_SPEC_RebasedCaptures18.state
  let thread := initialized 16384 (threadInner 1 0 0) old
  let tls := PV_LIB_SPEC_ThreadWords12.write thread 65496 16400
  let counter := PV_LIB_SPEC_ThreadWords12.write tls PV_LIB_SPEC_ThreadId13.counterOffset 1
  {counter with world := {counter.world with
    memory := fun address => if address=slot.physical then some 0 else counter.world.memory address
    live := fun address => address=16384 || old.world.live address
    allocator := {counter.world.allocator with metadata := fun address =>
      if address=16384 then (some {bytes := 48,alignment := ._Align1Shl3}) else old.world.allocator.metadata address}}}

def hooksSlot : Nat := 65504
def state : OWNER :=
  let cached := PV_LIB_SPEC_ThreadWords12.write tlsState
    PV_LIB_SPEC_StackSize14.minimumOffset 2097153
  let hooks := PV_LIB_SPEC_ThreadWords12.write cached hooksSlot 0
  {hooks with world := {hooks.world with memory := fun a => if a = hooksSlot + 8 then some 1 else hooks.world.memory a}}
def input : OwnInit.Input := {{PV_LIB_SPEC_ConcreteEntry.input with store := store} with world := state}


theorem memory_before (a : Nat) (bound : a<16384) :
    state.world.memory a = PV_LIB_SPEC_RebasedCaptures18.state.world.memory a := by
  change (if a = hooksSlot + 8 then some 1 else
    (PV_LIB_SPEC_ThreadWords12.write
      (PV_LIB_SPEC_ThreadWords12.write tlsState
        PV_LIB_SPEC_StackSize14.minimumOffset 2097153) hooksSlot 0).world.memory a) = _
  rw [if_neg (by dsimp [hooksSlot]; omega)]
  rw [PV_LIB_SPEC_ArcPhysical13.write_away _ hooksSlot 0 a
    (Or.inl (by dsimp [hooksSlot]; omega))]
  rw [PV_LIB_SPEC_ArcPhysical13.write_away _ PV_LIB_SPEC_StackSize14.minimumOffset 2097153 a
    (Or.inl (by dsimp [PV_LIB_SPEC_StackSize14.minimumOffset]; omega))]
  change (if a=slot.physical then some 0 else _) = _
  rw [if_neg (by dsimp [slot]; omega)]
  rw [PV_LIB_SPEC_ArcPhysical13.write_away _ PV_LIB_SPEC_ThreadId13.counterOffset 1 a
    (Or.inl (by dsimp [PV_LIB_SPEC_ThreadId13.counterOffset]; omega))]
  rw [PV_LIB_SPEC_ArcPhysical13.write_away _ 65496 16400 a (Or.inl (by omega))]
  simp only [PV_LIB_SPEC_AllocationImages.initialized,PV_LIB_SPEC_AllocationImages.overwrite,
    if_neg (by omega : ¬16384 ≤ a)]

#print axioms slot
#print axioms store
#print axioms tlsState
#print axioms hooksSlot
#print axioms state
#print axioms input
#print axioms memory_before
end PV_LIB_SPEC_RebasedEntry18
