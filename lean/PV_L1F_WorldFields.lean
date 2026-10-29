import R1Z.PV_OWN_WorldAdapter
set_option autoImplicit false
namespace PV_L1F_WorldFields
open R1Z.PV_W_Enriched R1Z.PV_OWN_Heap R1Z.PV_OWN_WorldAdapter
/-- Complete the heap adapter's explicit framing inventory: allocator state,
volatile writes, atomic order, fences and thread identity also survive. This
is the existing carrier operation, not a native allocator framing assertion. -/
theorem runtime_fields {Os Fs S X : Type} (w : World Os Fs S X) (h : Heap) :
 (commit w h).process.allocator=w.process.allocator ∧
 (commit w h).process.volatileWrites=w.process.volatileWrites ∧
 (commit w h).process.atomicOrder=w.process.atomicOrder ∧
 (commit w h).process.fences=w.process.fences ∧
 (commit w h).process.currentThread=w.process.currentThread := ⟨rfl,rfl,rfl,rfl,rfl⟩
#print axioms runtime_fields

/-- Updating the authoritative heap does not reset the same original OS or
filesystem, or alter a previously acquired ordered observer prior. -/
theorem prefix_frame {Os Fs S X C : Type} (w : World Os Fs S X) (h : Heap)
 (prior : List C) :
 ((commit w h).os,(commit w h).filesystem,prior)=(w.os,w.filesystem,prior) := rfl
#print axioms prefix_frame
end PV_L1F_WorldFields
