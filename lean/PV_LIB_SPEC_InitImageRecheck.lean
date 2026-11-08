import PV_LIB_SPEC_AllocationImages
import PV_LIB_SPEC_LocalInitMemory
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_InitImageRecheck
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner
open PV_OWN2_Codec (Pointer)
open PV_OWN2_ThreadInitStores PV_OWN2_WordImage
open PV_LIB_SPEC_AllocationImages

theorem first (s : OWNER) (h : Header) (handle callback vtable : Pointer) (i : Fin 8) :
    (initStores s h (pointerBytes handle) (pointerBytes callback) (pointerBytes vtable)).world.memory
      (h.pointer+i.val) = some (byte handle.val i.val).val := by
  simpa only [initStores,rawBytes,List.length_ofFn,List.getElem_ofFn,pointerBytes,byte,
    PV_LIB_SPEC_ArcImageGap.byte] using
    first_byte s h (rawBytes (pointerBytes handle)) (rawBytes (pointerBytes callback))
      (rawBytes (pointerBytes vtable)) i

theorem second (s : OWNER) (h : Header) (handle callback vtable : Pointer) (i : Fin 8) :
    (initStores s h (pointerBytes handle) (pointerBytes callback) (pointerBytes vtable)).world.memory
      (h.pointer+8+i.val) = some (byte callback.val i.val).val := by
  simpa only [initStores,rawBytes,List.length_ofFn,List.getElem_ofFn,pointerBytes,byte,
    PV_LIB_SPEC_ArcImageGap.byte] using
    second_byte s h (rawBytes (pointerBytes handle)) (rawBytes (pointerBytes callback))
      (rawBytes (pointerBytes vtable)) i

theorem third (s : OWNER) (h : Header) (handle callback vtable : Pointer) (i : Fin 8) :
    (initStores s h (pointerBytes handle) (pointerBytes callback) (pointerBytes vtable)).world.memory
      (h.pointer+16+i.val) = some (byte vtable.val i.val).val := by
  simpa only [initStores,rawBytes,List.length_ofFn,List.getElem_ofFn,pointerBytes,byte,
    PV_LIB_SPEC_ArcImageGap.byte,Nat.reduceAdd] using
    third_byte s h (rawBytes (pointerBytes handle)) (rawBytes (pointerBytes callback))
      (rawBytes (pointerBytes vtable)) i

/-- Recheck the old named24-byte initializer on EVERY pre-memory, including
stale allocator bytes. There is no padding in this object; its byte model needs
no sparse repair. This equates full memory functions, not just decoded words. -/
theorem memory_agreement (s : OWNER) (h : Header) (handle callback vtable : Pointer) :
    (initStores s h (pointerBytes handle) (pointerBytes callback) (pointerBytes vtable)).world.memory =
      overwrite h.pointer (threadInit handle.val callback.val vtable.val) s.world.memory := by
  funext address
  by_cases lower : h.pointer ≤ address
  · by_cases a : address < h.pointer+8
    · have i : address-h.pointer < 8 := by omega
      have cell := first s h handle callback vtable ⟨address-h.pointer,i⟩
      have eq : h.pointer+(address-h.pointer) = address := by omega
      rw [eq] at cell
      simpa only [overwrite,if_pos lower,threadInit,if_pos i,word,Option.getD_some] using cell
    · by_cases b : address < h.pointer+16
      · have i : address-(h.pointer+8) < 8 := by omega
        have cell := second s h handle callback vtable ⟨address-(h.pointer+8),i⟩
        have eq : h.pointer+8+(address-(h.pointer+8)) = address := by omega
        rw [eq] at cell
        have index : address-h.pointer-8 = address-(h.pointer+8) := by omega
        simpa only [overwrite,if_pos lower,threadInit,if_neg (by omega : ¬address-h.pointer<8),
          if_pos (by omega : address-h.pointer<16),word,Option.getD_some,index] using cell
      · by_cases c : address < h.pointer+24
        · have i : address-(h.pointer+16) < 8 := by omega
          have cell := third s h handle callback vtable ⟨address-(h.pointer+16),i⟩
          have eq : h.pointer+16+(address-(h.pointer+16)) = address := by omega
          rw [eq] at cell
          have index : address-h.pointer-16 = address-(h.pointer+16) := by omega
          simpa only [overwrite,if_pos lower,threadInit,if_neg (by omega : ¬address-h.pointer<8),
            if_neg (by omega : ¬address-h.pointer<16),if_pos (by omega : address-h.pointer<24),
            word,Option.getD_some,index] using cell
        · have frame := outside_frame s h (rawBytes (pointerBytes handle))
            (rawBytes (pointerBytes callback)) (rawBytes (pointerBytes vtable)) address
            (Or.inr (by simpa only [rawBytes,List.length_ofFn] using (show h.pointer+(8+8+8)≤address by omega)))
          simpa only [initStores,overwrite,if_pos lower,init_hole _ _ _ _ (by omega : 24≤address-h.pointer),Option.getD_none] using frame
  · have frame := outside_frame s h (rawBytes (pointerBytes handle))
        (rawBytes (pointerBytes callback)) (rawBytes (pointerBytes vtable)) address (Or.inl (by omega))
    simpa only [initStores,overwrite,if_neg lower] using frame

theorem initPost_memory (s : OWNER) (id p : Nat) (h : Header) (handle callback vtable : Pointer) :
    (PV_OWN2_BoxConstruction.initPost s id h p handle callback vtable).world.memory =
      overwrite p (threadInit handle.val callback.val vtable.val) s.world.memory := by
  unfold PV_OWN2_BoxConstruction.initPost
  rw [memory_agreement,PV_OWN2_BoxConstruction.headerStores_memory]
  rfl

#print axioms first
#print axioms second
#print axioms third
#print axioms memory_agreement
#print axioms initPost_memory
end PV_LIB_SPEC_InitImageRecheck
