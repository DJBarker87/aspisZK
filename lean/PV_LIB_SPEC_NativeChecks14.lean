import PV_LIB_SPEC_PrefixEnvironment14
import PV_LIB_SPEC_Values14
import PV_LIB_SPEC_ThreadWordRecheck12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_NativeChecks14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ThreadWords12 PV_LIB_SPEC_Entry14
open PV_LIB_SPEC_AllocationImages

def minimum : Pointer := ⟨2097153,by decide⟩
def zero : Pointer := ⟨0,by decide⟩

theorem minimum_bytes (i : Fin 8) :
    state.world.memory (PV_LIB_SPEC_StackSize14.minimumOffset+i.val) =
      some (PV_OWN2_WordImage.pointerBytes minimum i).val := by
  change (if PV_LIB_SPEC_StackSize14.minimumOffset+i.val=hooksSlot+8 then some 1 else
    (write (write PV_LIB_SPEC_Entry13.state PV_LIB_SPEC_StackSize14.minimumOffset 2097153)
      hooksSlot 0).world.memory (PV_LIB_SPEC_StackSize14.minimumOffset+i.val)) = _
  rw [if_neg (by dsimp [PV_LIB_SPEC_StackSize14.minimumOffset,hooksSlot]; have := i.isLt; omega)]
  rw [PV_LIB_SPEC_ArcPhysical13.write_away _ hooksSlot 0 _
    (Or.inr (by dsimp [PV_LIB_SPEC_StackSize14.minimumOffset,hooksSlot]; omega))]
  exact stored _ i _ _ _ (if_pos i.isLt)

theorem hook_bytes (i : Fin 8) : state.world.memory (hooksSlot+i.val) =
    some (PV_OWN2_WordImage.pointerBytes zero i).val := by
  change (if hooksSlot+i.val=hooksSlot+8 then some 1 else
    (write _ hooksSlot 0).world.memory (hooksSlot+i.val)) = _
  rw [if_neg (by have := i.isLt; omega)]
  exact stored _ i _ _ _ (if_pos i.isLt)

theorem minimum_word : read state PV_LIB_SPEC_StackSize14.minimumOffset = some minimum := by
  unfold PV_LIB_SPEC_ThreadWords12.read
  rw [show (fun i : Fin 8 => state.world.memory (PV_LIB_SPEC_StackSize14.minimumOffset+i.val)) =
    (fun i => some (PV_OWN2_WordImage.pointerBytes minimum i).val) from funext minimum_bytes,
    PV_OWN2_Codec.decode_pointer_image,PV_OWN2_WordImage.pointerBytes_value]

theorem hook_word : read state hooksSlot = some zero := by
  unfold PV_LIB_SPEC_ThreadWords12.read
  rw [show (fun i : Fin 8 => state.world.memory (hooksSlot+i.val)) =
    (fun i => some (PV_OWN2_WordImage.pointerBytes zero i).val) from funext hook_bytes,
    PV_OWN2_Codec.decode_pointer_image,PV_OWN2_WordImage.pointerBytes_value]

theorem empty_tls : PV_LIB_SPEC_SpawnHooks14.empty hooksSlot state = some () := by
  unfold PV_LIB_SPEC_SpawnHooks14.empty
  rw [hook_word]
  change (if zero.val=0 ∧ state.world.memory (hooksSlot+8)=some 1 then some () else none) = some ()
  exact if_pos ⟨rfl,rfl⟩

/-- Stack-size is computed from the SAME entry world's cached word, not a
constant substituted into the native schedule. Still a local request check. -/
theorem size_value : PV_LIB_SPEC_StackSize14.value PV_LIB_SPEC_PrefixEnvironment14.parameters state
    [PV_THR2_KeyValues.pack PV_LIB_SPEC_Builder269.sizeKind [],
     PV_THR2_KeyValues.pack PV_LIB_SPEC_StackSize14.closureKind []] = some (.number 2097152) := by
  unfold PV_LIB_SPEC_StackSize14.value
  simp only [ne_eq,not_true_eq_false,ite_false]
  change (do let cached ← read state PV_LIB_SPEC_StackSize14.minimumOffset
             if cached.val=0 then none else some (Data.number (cached.val-1))) = _
  rw [minimum_word]
  rfl

/-- Exact f454 argument shape, using the initialized current Thread's numeric
facet. This is a LOCAL poll, not an original-entry reachability assertion. -/
def config : Config :=
  ⟨{activation := 7,remaining := []},[],
    PV_STX2_Store.write PV_LIB_SPEC_Entry13.store ⟨7,10,[]⟩ (some (.number 16384))⟩
def arguments : List Data := [PV_STX2_TypedReferences.reference ⟨7,10,[]⟩ .null]

theorem thread_value : PV_LIB_SPEC_SpawnHooks14.thread
    PV_LIB_SPEC_PrefixEnvironment14.parameters config state arguments = some 16384 := by
  change (do let ptr ← PV_THR2_OwnInitPointerCodec.decode (.number 16384)
             if ptr.val=0 then none else some ptr.val) = _
  rfl

theorem hooks_reply (native : PV_LIB_SPEC_PhysicalStack12.Frame) (events : List Event) :
    PV_LIB_SPEC_SpawnHooks14.reply native hooksSlot PV_LIB_SPEC_PrefixEnvironment14.parameters
      config state arguments ⟨.returned (.ok .null),state,events⟩ =
      some ⟨.returned (.ok PV_LIB_SPEC_SpawnHooks14.value),
        PV_LIB_SPEC_PhysicalStack12.installDefault native state,events⟩ := by
  unfold PV_LIB_SPEC_SpawnHooks14.reply
  rw [thread_value]
  change (do let _ ← PV_LIB_SPEC_SpawnHooks14.empty hooksSlot state
             pure (PV_LIB_SPEC_SpawnHooks14.result native state
               (⟨.returned (.ok .null),state,events⟩ : Reply OWNER Event Data))) = _
  rw [empty_tls]
  rfl

#print axioms minimum
#print axioms zero
#print axioms minimum_bytes
#print axioms hook_bytes
#print axioms minimum_word
#print axioms hook_word
#print axioms empty_tls
#print axioms size_value
#print axioms config
#print axioms arguments
#print axioms thread_value
#print axioms hooks_reply
end PV_LIB_SPEC_NativeChecks14
