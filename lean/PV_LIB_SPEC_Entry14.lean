import PV_LIB_SPEC_EntryPre13
import PV_LIB_SPEC_SpawnHooks14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Entry14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
/-- Finite initial native state: previously cached2MiB minimum and initialized
empty SPAWN_HOOKS at fs:-0x20. These are entry data. No hook execution,
original native/source call-stack correspondence or successful run is claimed. -/
def hooksSlot : Nat := 65504
def state : OWNER :=
  let cached := PV_LIB_SPEC_ThreadWords12.write PV_LIB_SPEC_Entry13.state
    PV_LIB_SPEC_StackSize14.minimumOffset 2097153
  let hooks := PV_LIB_SPEC_ThreadWords12.write cached hooksSlot 0
  {hooks with world := {hooks.world with memory := fun a => if a = hooksSlot + 8 then some 1 else hooks.world.memory a}}
def input : OwnInit.Input := {PV_LIB_SPEC_Entry13.input with world := state}

theorem memory_before (a : Nat) (bound : a<16384) :
    state.world.memory a = PV_LIB_SPEC_ConcreteCaptures.state.world.memory a := by
  change (if a = hooksSlot + 8 then some 1 else
    (PV_LIB_SPEC_ThreadWords12.write
      (PV_LIB_SPEC_ThreadWords12.write PV_LIB_SPEC_Entry13.state
        PV_LIB_SPEC_StackSize14.minimumOffset 2097153) hooksSlot 0).world.memory a) = _
  rw [if_neg (by dsimp [hooksSlot]; omega)]
  rw [PV_LIB_SPEC_ArcPhysical13.write_away _ hooksSlot 0 a
    (Or.inl (by dsimp [hooksSlot]; omega))]
  rw [PV_LIB_SPEC_ArcPhysical13.write_away _ PV_LIB_SPEC_StackSize14.minimumOffset 2097153 a
    (Or.inl (by dsimp [PV_LIB_SPEC_StackSize14.minimumOffset]; omega))]
  exact PV_LIB_SPEC_EntryPre13.memory_before a bound

#print axioms hooksSlot
#print axioms state
#print axioms input
#print axioms memory_before
end PV_LIB_SPEC_Entry14
