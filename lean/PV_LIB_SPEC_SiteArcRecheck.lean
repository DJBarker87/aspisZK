import PV_LIB_SPEC_SiteRuntime
import PV_LIB_SPEC_ScopeAllocationPollGap
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_SiteArcRecheck
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_SPEC_ScopeAllocationGap
open PV_LIB_SPEC_SiteArc

def panic (atomicKind cellKind : Data) : Data :=
  PV_THR2_KeyValues.pack atomicKind [PV_THR2_KeyValues.pack cellKind [.boolean false]]

/-- Local codec graph, with actual source ScopeData field order. Every source
thread-pointer interpretation result is retained, including missing backing.
This does not assume a decoder succeeds at a future source continuation. -/
theorem scope_image (w : OWNER) (thread atomicKind cellKind : Data) :
    image C K w .scope (atomic 1) (atomic 1)
      (PV_THR2_ScopeData.value (atomic 0) thread (panic atomicKind cellKind)) =
      (threadWord C w thread).map PV_LIB_SPEC_AllocationImages.scope := by
  change (do let pointer ← threadWord C w thread
             pure (PV_LIB_SPEC_AllocationImages.scope pointer)) = _
  cases threadWord C w thread <;> rfl

/-- Source-correct40-byte resource data from the old counterexample is NOW
queried. The result is the exact codec graph; the old incorrect48-byte pending
request is gone. Original-entry thread/AtomicBool binding remains to be proved. -/
theorem scope_handler (encode : Encode) (s : Store Data)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (w : OWNER) (thread atomicKind cellKind : Data) :
    handler C K PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources encode s H
      (PV_LIB_SPEC_ScopeAllocationPollGap.request s thread (panic atomicKind cellKind)) w =
      (threadWord C w thread).map (fun pointer =>
        reply PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources encode s w .scope
          (PV_LIB_SPEC_AllocationImages.scope pointer)) := by
  have resource := (PV_THR2_PacketBoxResource.answer
    PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources encode s w (shape .scope) 8).trans
      (PV_LIB_SPEC_ScopeAllocationPollGap.correct40 (world w))
  simp only [PV_LIB_SPEC_SiteArc.handler,PV_LIB_SPEC_ScopeAllocationPollGap.request,PV_THR2_KeyValues.pack,
    List.map_cons,List.map_nil,and_self,ite_true]
  rw [show classify (PV_THR2_ScopeData.value (atomic 0) thread (panic atomicKind cellKind)) =
      some .scope from scope_classified _ _ _]
  simp only [resource,if_neg (by decide : ¬(16384:Nat)=0),scope_image,Option.map_map]
  rfl

/-- Packet's native image/reply is unchanged at its OWN source type. The new
ScopeData dispatch does not coerce its40-byte layout to Packet48. -/
theorem packet_reply (resources : Resources) (encode : Encode) (s : Store Data)
    (w : OWNER) (scopePointer : Nat) :
    reply resources encode s w .packet (PV_LIB_SPEC_AllocationImages.packet scopePointer) =
      PV_LIB_SPEC_SparseArc.reply resources encode s w scopePointer := by
  simp only [reply,shape,PV_LIB_SPEC_SparseArc.reply,PV_LIB_SPEC_AllocationImages.packet_agreement]
  rfl

#print axioms panic
#print axioms scope_image
#print axioms scope_handler
#print axioms packet_reply
end PV_LIB_SPEC_SiteArcRecheck
