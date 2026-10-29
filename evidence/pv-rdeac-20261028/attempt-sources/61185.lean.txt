import R1Z.PV_RDEAC_EndpointInstance
import R1Z.PV_RDEAC_Frames
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_CleanupHeaders
open PV_RDB1_V183_ReserveWorld

theorem append_success {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer U8) (tail : List U8) (w : World S F)
    (h : (PV_RDEAC_FullAppend.append step shape b tail w).returned=.ok ()) :
    (PV_RDEAC_FullAppend.append step shape b tail w).buffer.capacity=
      PV_RDEA_AppendRequests.nextCapacity b.values.length b.capacity tail.length ∧
    (PV_RDEAC_FullAppend.append step shape b tail w).buffer.values=b.values++tail := by
  let e := PV_RDEAC_FullAppend.append step shape b tail w
  change e.returned=.ok () at h
  have he : (PV_RDEAC_FullAppend.erase e).1=.ok e.buffer := by simp only [PV_RDEAC_FullAppend.erase,h]
  rw [PV_RDEAC_FullAppend.projection] at he
  have header := PV_RDEA_ExecutionHeaders.append_header step shape b tail w e.buffer he
  exact ⟨header.2,header.1⟩

theorem clone_success {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address : Nat) (base : List U8) (w : World S F)
    (h : (PV_RDEAC_FullClone.clone step shape address base w).returned=.ok ()) :
    (PV_RDEAC_FullClone.clone step shape address base w).buffer.capacity=base.length ∧
    (PV_RDEAC_FullClone.clone step shape address base w).buffer.values=base := by
  let e := PV_RDEAC_FullClone.clone step shape address base w
  change e.returned=.ok () at h
  have he : (PV_RDEAC_FullAppend.erase e).1=.ok e.buffer := by simp only [PV_RDEAC_FullAppend.erase,h]
  rw [PV_RDEAC_FullClone.projection] at he
  have header := PV_RDEA_ExecutionHeaders.clone_header step shape address base w e.buffer he
  exact ⟨header.2,header.1⟩

theorem owned_header {S F : Type} (free : Nat → Nat → Nat → S → S)
    (b : Buffer U8) (w : World S F) (cap : b.capacity=69) :
    (PV_RDEAC_OwnedCleanup.release free b w).allocator=free b.address 69 1 w.allocator ∧
    (PV_RDEAC_OwnedCleanup.release free b w).deallocCalls=w.deallocCalls+1 ∧
    (PV_RDEAC_OwnedCleanup.release free b w).frame=w.frame := by
  have e := PV_RDEAC_OwnedCleanup.allocated free b w (by omega)
  rw [cap] at e
  exact ⟨e.1,e.2.1,(PV_RDEAC_OwnedCleanup.effects free b w).1⟩

#print axioms append_success
#print axioms clone_success
#print axioms owned_header
end R1Z.PV_RDEAC_CleanupHeaders
