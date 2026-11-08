import PV_LIB_SPEC_ActiveHistory18620
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_MemoryWindow20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ThreadWords12

/-- Byte-for-byte qword transport; no unwritten byte is initialized. -/
theorem read_congr (left right : OWNER) (base : Nat)
    (same : ∀ i : Fin 8, left.world.memory (base+i.val) = right.world.memory (base+i.val)) :
    PV_LIB_SPEC_ThreadWords12.read left base = PV_LIB_SPEC_ThreadWords12.read right base := by
  unfold PV_LIB_SPEC_ThreadWords12.read
  exact congrArg PV_OWN2_Codec.decodePointer (funext same)

theorem set_byte (slot : PV_LIB_SPEC_TlsBindings13.Slot) (w : OWNER) (b : Bool) (base : Nat)
    (outside : ∀ i : Fin 8, base+i.val ≠ slot.physical) :
    PV_LIB_SPEC_ThreadWords12.read (PV_LIB_SPEC_CellPhysical13.setByte slot w b) base = PV_LIB_SPEC_ThreadWords12.read w base :=
  read_congr _ _ base (fun i => PV_LIB_SPEC_CellPhysical13.away slot w b (base+i.val) (outside i))

theorem sparse_word (w : OWNER) (writeBase value base : Nat)
    (outside : ∀ i : Fin 8, base+i.val<writeBase ∨ writeBase+8≤base+i.val) :
    PV_LIB_SPEC_ThreadWords12.read (PV_LIB_SPEC_ThreadWords12.write w writeBase value) base = PV_LIB_SPEC_ThreadWords12.read w base :=
  read_congr _ _ base (fun i => PV_LIB_SPEC_ArcPhysical13.write_away w writeBase value (base+i.val) (outside i))

/-- Complete physical world after the actual original callback delivery. -/
theorem world186 (e : PV_LIB_SPEC_EntryWorld18.Entry) (a : Nat) :
    (PV_LIB_SPEC_ActiveAdoption19.history e a 186).state.current.world =
      PV_LIB_SPEC_CellPhysical13.setByte PV_LIB_SPEC_Entry13.slot e.world true := by
  rw [PV_LIB_SPEC_ActiveHistory18620.original186]
  exact (PV_LIB_SPEC_ActiveBoundary19.effects
    (PV_LIB_SPEC_ActiveConsumption19.bound (PV_LIB_SPEC_ActiveOrigin18520.origin e a))
    (PV_LIB_A_F5CallbackStall16.config PV_LIB_SPEC_ActiveForward20.store176
      PV_LIB_A_F5FullEntry16.activation PV_LIB_A_F5FullEntry16.parents PV_LIB_SPEC_Entry13.slot.source)
    (PV_LIB_A_F5CallbackStall16.wait PV_LIB_SPEC_ActiveForward20.store176 PV_LIB_SPEC_Entry13.slot.source)
    ⟨.returned (.ok (.boolean false)),PV_LIB_SPEC_CellPhysical13.setByte PV_LIB_SPEC_Entry13.slot e.world true,[]⟩).1

theorem original_window (e : PV_LIB_SPEC_EntryWorld18.Entry) (a base : Nat)
    (outside : ∀ i : Fin 8, base+i.val ≠ PV_LIB_SPEC_Entry13.slot.physical) :
    PV_LIB_SPEC_ThreadWords12.read (PV_LIB_SPEC_ActiveAdoption19.history e a 186).state.current.world base = PV_LIB_SPEC_ThreadWords12.read e.world base := by
  rw [world186]
  exact set_byte _ _ _ base outside

#print axioms read_congr
#print axioms set_byte
#print axioms sparse_word
#print axioms world186
#print axioms original_window
end PV_LIB_SPEC_MemoryWindow20
