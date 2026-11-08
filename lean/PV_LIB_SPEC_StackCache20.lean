import PV_LIB_SPEC_MemoryWindow20
import PV_LIB_SPEC_Stack295Route20
import PV_LIB_SPEC_StackCacheLaw20
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_StackCache20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ThreadWords12
open PV_LIB_SPEC_StackSize14 (minimumOffset)

def cached : Pointer := ⟨2097153,by decide⟩
def args : List Data :=
  [PV_THR2_KeyValues.pack PV_LIB_SPEC_Builder269.sizeKind [],
    PV_THR2_KeyValues.pack PV_LIB_SPEC_StackSize14.closureKind []]

/-- Exact finite initialized cache of the physically valid concrete entry. -/
theorem entry_cache : PV_LIB_SPEC_ThreadWords12.read PV_LIB_SPEC_EntryWorld18.concrete.world minimumOffset = some cached := by
  have same : PV_LIB_SPEC_ThreadWords12.read PV_LIB_SPEC_DisjointEntry18.state minimumOffset =
      PV_LIB_SPEC_ThreadWords12.read (PV_LIB_SPEC_ThreadWords12.write PV_LIB_SPEC_DisjointEntry18.tlsState minimumOffset cached.val) minimumOffset := by
    apply PV_LIB_SPEC_MemoryWindow20.read_congr
    intro i
    change (if minimumOffset+i.val=PV_LIB_SPEC_DisjointEntry18.hooksSlot+8 then some 1 else
      (PV_LIB_SPEC_ThreadWords12.write (PV_LIB_SPEC_ThreadWords12.write PV_LIB_SPEC_DisjointEntry18.tlsState minimumOffset cached.val)
        PV_LIB_SPEC_DisjointEntry18.hooksSlot 0).world.memory (minimumOffset+i.val)) = _
    rw [if_neg (by dsimp [minimumOffset,PV_LIB_SPEC_DisjointEntry18.hooksSlot]; omega)]
    exact PV_LIB_SPEC_ArcPhysical13.write_away _ _ _ _
      (Or.inr (by dsimp [minimumOffset,PV_LIB_SPEC_DisjointEntry18.hooksSlot]; omega))
  exact same.trans (read_written _ _ cached)

/-- The same cache survives the REAL original callback's physical PV_LIB_SPEC_ThreadWords12.write. -/
theorem original_cache (a : Nat) :
    PV_LIB_SPEC_ThreadWords12.read (PV_LIB_SPEC_ActiveAdoption19.history PV_LIB_SPEC_EntryWorld18.concrete a 186).state.current.world
      minimumOffset = some cached := by
  rw [PV_LIB_SPEC_MemoryWindow20.original_window _ a minimumOffset
    (by intro i; dsimp [minimumOffset,PV_LIB_SPEC_Entry13.slot]; omega)]
  exact entry_cache

#print axioms cached
#print axioms args
#print axioms entry_cache
#print axioms original_cache
end PV_LIB_SPEC_StackCache20
