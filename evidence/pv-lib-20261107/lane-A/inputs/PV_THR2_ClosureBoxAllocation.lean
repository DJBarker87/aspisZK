import PV_THR2_PacketBoxResourceOwned
import PV_OWN2_ClientLayout
set_option autoImplicit false
noncomputable section
namespace PV_THR2_ClosureBoxAllocation
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner R1Z.PV_FXM_ReserveWorld
/-- Named fc8808eb callback layout, distinct from24-byte ThreadInit and the
ArcInner allocation. Covered native_workers instantiations only, as recorded
by PV_OWN2_ClientLayout; conditional on amended-translator acceptance. -/
def shape : Shape := ⟨PV_OWN2_ClientLayout.layout.callbackSize,._Align1Shl3⟩
/-- Complete callback allocation reply. The actual issued source store supplies
its minted backing; no source store is replaced. Initialization bytes are a
separate source-value association, not claimed by this definition. -/
def reply (resources : Resources) (encode : Encode) (s : Store Data) (w : OWNER) :=
  PV_THR2_PacketBoxReply.finish s w.next
    (PV_EVHB_SourceLifetimes.emptyHeader shape PV_OWN2_ClientLayout.layout.alignment)
    (PV_THR2_PacketBoxResource.reply resources encode s w shape PV_OWN2_ClientLayout.layout.alignment)
/-- Resource request size is consumed from ClientLayout BY NAME; no new
layout or pointer-shape hypothesis. -/
theorem request_size : shape.width = PV_OWN2_ClientLayout.layout.callbackSize := rfl
/-- Registration is exactly the actual source-minted child argument backing. -/
theorem registered (s : Store Data) (w : OWNER) :
    receiver (PV_THR2_PacketBoxRegister.pre s w shape PV_OWN2_ClientLayout.layout.alignment)
      (PV_THR2_PacketBoxRegister.place s) =
      some (w.next,PV_EVHB_SourceLifetimes.emptyHeader shape PV_OWN2_ClientLayout.layout.alignment) :=
  PV_THR2_PacketBoxRegister.registered s w shape _
/-- Consume existing named general allocation facts. Success is one actual
resource branch; null, fault, divergence, failure and pending remain in reply.
No native image or original-entry installation is asserted. -/
theorem returned (resources : Resources) (encode : Encode) (s : Store Data) (w : OWNER) (p : Nat)
    (answer : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer = .returned (.ok p))
    (nonnull : p ≠ 0) :
    (reply resources encode s w).answer = .returned (.ok (PV_THR2_PacketBoxReply.value s)) ∧
      OwnedAt (reply resources encode s w).world.world w.next := by
  exact PV_THR2_PacketBoxResourceOwned.returned resources encode s w shape _ p answer nonnull
/-- The logical returned pointer is derived from the actual argument activation;
the physical allocation address stays in its OWNER header. -/
theorem pointer (s : Store Data) :
    PV_THR2_PacketBoxReply.value s =
      PV_STX2_TypedReferences.reference ⟨s.nextActivation,1,[]⟩ .null := rfl
#print axioms request_size
#print axioms registered
#print axioms returned
#print axioms pointer
end PV_THR2_ClosureBoxAllocation
