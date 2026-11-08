import PV_LIB_SPEC_NativeModel
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_WordThreadRecheck
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_SPEC_ScopeAllocationGap PV_LIB_SPEC_WordThreadArc

theorem scope_handler (encode : Encode) (s : Store Data)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (w : OWNER) (word : PV_OWN2_Codec.Pointer) (atomicKind cellKind : Data) :
    handler C K PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources encode s H
      (PV_LIB_SPEC_ScopeAllocationPollGap.request s
        (PV_THR2_OwnInitPointerCodec.encode word) (PV_LIB_SPEC_SiteArcRecheck.panic atomicKind cellKind)) w =
      some (reply PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources encode s w .scope
        (PV_LIB_SPEC_AllocationImages.scope word.val)) := by
  have resource := (PV_THR2_PacketBoxResource.answer
    PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources encode s w (shape .scope) 8).trans
      (PV_LIB_SPEC_ScopeAllocationPollGap.correct40 (world w))
  simp only [PV_LIB_SPEC_WordThreadArc.handler,PV_LIB_SPEC_ScopeAllocationPollGap.request,PV_THR2_KeyValues.pack,
    List.map_cons,List.map_nil,and_self,ite_true]
  rw [show classify (PV_THR2_ScopeData.value (atomic 0)
      (PV_THR2_OwnInitPointerCodec.encode word) (PV_LIB_SPEC_SiteArcRecheck.panic atomicKind cellKind)) =
      some .scope from scope_classified _ _ _]
  simp only [resource,if_neg (by decide : ¬(16384:Nat)=0),scope_image_word,Option.map_some]

/-- No change at Packet operands: all full replies and complete memory agree
with the existing sparse Packet model, including its16-byte no-store tail. -/
theorem packet_reply (resources : Resources) (encode : Encode) (s : Store Data)
    (w : OWNER) (scopePointer : Nat) :
    reply resources encode s w .packet (PV_LIB_SPEC_AllocationImages.packet scopePointer) =
      PV_LIB_SPEC_SparseArc.reply resources encode s w scopePointer := by
  simp only [reply,shape,PV_LIB_SPEC_SparseArc.reply,PV_LIB_SPEC_AllocationImages.packet_agreement]
  rfl

/-- The new codec actually accepts every inhabitant of the retained native
Thread facet; this contrasts with the old incompatible theorem55108. It is a
LOCAL graph statement, not a discharge of Shape at an original-entry call. -/
theorem thread_shape (w : OWNER) (thread : Data)
    (shaped : PV_THR2_TypedRepresentation_Thread.Shape thread) :
    ∃ word : PV_OWN2_Codec.Pointer,
      thread = PV_THR2_OwnInitPointerCodec.encode word ∧
      threadWord C w thread = some word.val := by
  obtain ⟨word,rfl⟩ := shaped
  exact ⟨word,rfl,thread_word _ _ _⟩

#print axioms scope_handler
#print axioms packet_reply
#print axioms thread_shape
end PV_LIB_SPEC_WordThreadRecheck
