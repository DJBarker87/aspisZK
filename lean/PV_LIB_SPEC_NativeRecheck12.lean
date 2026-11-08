import PV_LIB_SPEC_NativeBindings12
import PV_LIB_SPEC_SuccessSchedule12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_NativeRecheck12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_SPEC_ScopeAllocationGap PV_LIB_SPEC_NativeBoolArc

theorem scope_handler (encode : Encode) (s : Store Data)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (w : OWNER) (word : PV_OWN2_Codec.Pointer) (atomicKind cellKind : Data) :
    handler C K PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources encode s H
      (PV_LIB_SPEC_ScopeAllocationPollGap.request s
        (PV_THR2_OwnInitPointerCodec.encode word) (PV_LIB_SPEC_AtomicBoolGap.zero atomicKind cellKind)) w =
      some (reply PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources encode s w .scope
        (PV_LIB_SPEC_AllocationImages.scope word.val)) := by
  have resource := (PV_THR2_PacketBoxResource.answer
    PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources encode s w (shape .scope) 8).trans
      (PV_LIB_SPEC_ScopeAllocationPollGap.correct40 (world w))
  simp only [PV_LIB_SPEC_NativeBoolArc.handler,PV_LIB_SPEC_ScopeAllocationPollGap.request,PV_THR2_KeyValues.pack,
    List.map_cons,List.map_nil,and_self,ite_true]
  rw [show classify (PV_THR2_ScopeData.value (atomic 0)
      (PV_THR2_OwnInitPointerCodec.encode word) (PV_LIB_SPEC_AtomicBoolGap.zero atomicKind cellKind)) =
      some .scope from scope_classified _ _ _]
  simp only [resource,if_neg (by decide : ¬(16384:Nat)=0),scope_image_u8,Option.map_some]

/-- No change at Packet operands: all full replies and complete memory agree
with the existing sparse Packet model, including its16-byte no-store tail. -/
theorem packet_reply (resources : Resources) (encode : Encode) (s : Store Data)
    (w : OWNER) (scopePointer : Nat) :
    reply resources encode s w .packet (PV_LIB_SPEC_AllocationImages.packet scopePointer) =
      PV_LIB_SPEC_SparseArc.reply resources encode s w scopePointer := by
  simp only [reply,shape,PV_LIB_SPEC_SparseArc.reply,PV_LIB_SPEC_AllocationImages.packet_agreement]
  rfl

def boolFn : Data := match PV_THR2_F6.node20 with
  | .leaf (.call _ fn _ _ _) => fn | _ => .null
def cellFn : Data := match PV_THR2_F361.node62 with
  | .leaf (.call _ fn _ _ _) => fn | _ => .null
def danglingFn : Data := match PV_THR2_F361.node82 with
  | .leaf (.call _ fn _ _ _) => fn | _ => .null

theorem bool_value (b : Bool) :
    PV_LIB_SPEC_NativeConstructors.value boolFn [.boolean b] =
      some (PV_LIB_SPEC_NativeConstructors.atomicBool b) := rfl

theorem cell_value (v : Data) :
    PV_LIB_SPEC_NativeConstructors.value cellFn [v] =
      some (PV_THR2_KeyValues.pack PV_LIB_SPEC_NativeKinds.unsafeCell [v]) := rfl

theorem dangling_value (v : Data) :
    PV_LIB_SPEC_NativeConstructors.value danglingFn [v] =
      some (PV_THR2_KeyValues.pack PV_LIB_SPEC_NativeKinds.maybeDangling [v]) := rfl

/-- The source13123 constructor actually supplies the wrapper projected by
CallbackOperands. Physical &run is still resolved from the reached registry. -/
theorem capture_constructor (p : PV_LIB_SPEC_Frozen.Parameters) (w : OWNER)
    (reference : Data) (k : Nat) :
    PV_LIB_SPEC_CallbackOperands.captureWords (PV_LIB_SPEC_Frozen.runtime p).carrier w
      (PV_THR2_KeyValues.pack PV_LIB_SPEC_NativeKinds.maybeDangling
        [PV_THR2_KeyValues.pack
          (match PV_THR2_F15.node34 with | .leaf (.aggregateMove _ _ kind _) => kind | _ => .null)
          [reference,.number k]]) =
      (PV_LIB_SPEC_SparsePacketHandler.physical (PV_LIB_SPEC_Frozen.runtime p).carrier w reference).map
        (fun pointer => (pointer,k)) :=
  PV_LIB_SPEC_CallbackOperands.capture_graph p w _ reference k

#print axioms boolFn
#print axioms cellFn
#print axioms danglingFn
#print axioms bool_value
#print axioms cell_value
#print axioms dangling_value
#print axioms capture_constructor
#print axioms scope_handler
#print axioms packet_reply

end PV_LIB_SPEC_NativeRecheck12
