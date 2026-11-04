import PV_EVHB_RawVecOwner
import R1Z.PV_RunJoin_AllocatorWorld63
/-! Explicit projection from source slots to V183. This exposes precisely what
V183 already preserves and what a source-bound allocator-side owner registry
must additionally deliver. It does not assume an equality of world types. -/
set_option autoImplicit false
namespace PV_EVHB_RawVecProjection
open Aeneas Aeneas.Std R1Z.PV_FXM_ReserveWorld PV_EVHB_RawVecOwner

def eraseSlots {S F : Type} (w : NativeWorld S F) : World (Heap S) F :=
  {allocator := w.allocator
   allocCalls := w.allocCalls
   reallocCalls := w.reallocCalls
   deallocCalls := w.deallocCalls
   successfulAlloc := w.successfulAlloc
   successfulRealloc := w.successfulRealloc
   drops := w.drops
   history := w.history
   memory := w.memory
   live := w.live
   frame := w.frame.rest}

theorem erase_install {S F : Type} (w : NativeWorld S F) (owner : Nat)
    (h : Header) (pointer cap : Nat) :
    eraseSlots (install w owner h pointer cap)=eraseSlots w := rfl

theorem erase_allocated {S F : Type} (w : NativeWorld S F) (h : Header)
    (pointer cap : Nat) (backend : S) :
    eraseSlots (allocated w h pointer cap backend)=
      succeeded (request h cap) pointer
        (attempted (request h cap) (some pointer)
          ⟨backend,resizedMetadata w.allocator h pointer cap⟩ (eraseSlots w)) := rfl

theorem erase_denied {S F : Type} (w : NativeWorld S F) (h : Header)
    (cap : Nat) (backend : S) :
    eraseSlots (denied w h cap backend)=
      attempted (request h cap) none ⟨backend,w.allocator.metadata⟩ (eraseSlots w) := rfl

theorem native_frame {A S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer A) (n : Nat)
    (w : World S F) : (native step wordMax byteMax shape b n w).world.frame=w.frame := by
  unfold native growExact finish
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  dsimp only
  cases step ⟨b.address,b.capacity,b.values.length+n,shape⟩ w.allocator with
  | mk p s => cases p <;> rfl

theorem execute_frame [ProverRwFull.ExternalTypes] {A S F : Type}
    (runtime : R1Z.PV_RunJoin_AllocatorWorld63.Runtime S F)
    (w : World S F) (v : alloc.vec.Vec A) (n : Usize) :
    (R1Z.PV_RunJoin_AllocatorWorld63.execute runtime w v n).world.frame=w.frame :=
  native_frame _ _ _ _ _ _ _

#print axioms erase_install
#print axioms erase_allocated
#print axioms erase_denied
#print axioms native_frame
#print axioms execute_frame
end PV_EVHB_RawVecProjection
