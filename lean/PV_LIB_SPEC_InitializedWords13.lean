import PV_LIB_SPEC_EntryPre13
import PV_LIB_SPEC_ThreadWordRecheck12
import PV_LIB_SPEC_ArcPhysical13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_InitializedWords13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Entry13
open PV_LIB_SPEC_ThreadWords12
open PV_LIB_SPEC_AllocationImages

def one : Pointer := ⟨1,by decide⟩
def inner : Pointer := ⟨16400,by decide⟩

theorem counter_bytes (i : Fin 8) :
    state.world.memory (PV_LIB_SPEC_ThreadId13.counterOffset+i.val) =
      some (PV_OWN2_WordImage.pointerBytes one i).val := by
  have final : PV_LIB_SPEC_ThreadId13.counterOffset+i.val≠65520 := by
    dsimp [PV_LIB_SPEC_ThreadId13.counterOffset]; omega
  change (if PV_LIB_SPEC_ThreadId13.counterOffset+i.val=65520 then some 0 else
    (write _ PV_LIB_SPEC_ThreadId13.counterOffset 1).world.memory
      (PV_LIB_SPEC_ThreadId13.counterOffset+i.val)) = _
  rw [if_neg final]
  apply stored
  exact if_pos i.isLt

theorem tls_bytes (i : Fin 8) : state.world.memory (65496+i.val) =
    some (PV_OWN2_WordImage.pointerBytes inner i).val := by
  have final : 65496+i.val≠65520 := by have := i.isLt; omega
  change (if 65496+i.val=65520 then some 0 else
    (write _ PV_LIB_SPEC_ThreadId13.counterOffset 1).world.memory (65496+i.val)) = _
  rw [if_neg final]
  have away := PV_LIB_SPEC_ArcPhysical13.write_away
    (write (initialized 16384 (threadInner 1 0 0) PV_LIB_SPEC_ConcreteCaptures.state) 65496 16400)
    PV_LIB_SPEC_ThreadId13.counterOffset 1 (65496+i.val)
    (Or.inl (by dsimp [PV_LIB_SPEC_ThreadId13.counterOffset]; have := i.isLt; omega))
  rw [away]
  apply stored
  exact if_pos i.isLt

theorem counter : read state PV_LIB_SPEC_ThreadId13.counterOffset = some one := by
  unfold PV_LIB_SPEC_ThreadWords12.read
  rw [show (fun i : Fin 8 => state.world.memory (PV_LIB_SPEC_ThreadId13.counterOffset+i.val)) =
    (fun i => some (PV_OWN2_WordImage.pointerBytes one i).val) from funext counter_bytes,
    PV_OWN2_Codec.decode_pointer_image,PV_OWN2_WordImage.pointerBytes_value]

theorem tls : read state 65496 = some inner := by
  unfold PV_LIB_SPEC_ThreadWords12.read
  rw [show (fun i : Fin 8 => state.world.memory (65496+i.val)) =
    (fun i => some (PV_OWN2_WordImage.pointerBytes inner i).val) from funext tls_bytes,
    PV_OWN2_Codec.decode_pointer_image,PV_OWN2_WordImage.pointerBytes_value]

/-- Source/thread-id value2 is computed from initialized physical COUNTER1.
The same initial world satisfies the complete original entry Pre (EntryPre13).
Still no claim of reaching native452 from that entry. -/
theorem id_value : PV_LIB_SPEC_ThreadId13.value 0 state =
    some (2,write state PV_LIB_SPEC_ThreadId13.counterOffset 2) := by
  unfold PV_LIB_SPEC_ThreadId13.value
  rw [Nat.zero_add,counter]
  rfl

#print axioms one
#print axioms inner
#print axioms counter_bytes
#print axioms tls_bytes
#print axioms counter
#print axioms tls
#print axioms id_value
end PV_LIB_SPEC_InitializedWords13
