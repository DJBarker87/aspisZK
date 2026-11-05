import NIJ_NativeSdkRelease
import S2W_ReturnedCheckpoint
set_option autoImplicit false
namespace NIJ_ReturnedWrite
open Aeneas Aeneas.Std AspisR1 AspisR1.S2Trust AspisR1.S2W_D189Entry
open AspisR1.S2W_TrustedStd AspisR1.S2W_ReturnedCheckpoint
open AspisR1.S2W_CommittedCheckpoint AspisR1.S2W_EntryWriteHistory

theorem bytes (e : Entry) (account : Nat) (saved : alloc.vec.Vec U8)
 (size : (e.heap.payload (e.heap.accounts account).1).descriptor.length = saved.val.length) :
 payloadBytes encode ((copyHeap e.heap (e.heap.accounts account).1
  (source (nativeBytes saved))).payload (e.heap.accounts account).1) saved.val.length =
 AspisR1.MultiproofConeCanonical.bytesOf saved.val := by
 rw [← vector_representation saved]
 have point : payloadBytes encode ((copyHeap e.heap (e.heap.accounts account).1
  (source (nativeBytes saved))).payload (e.heap.accounts account).1) saved.val.length =
  payloadBytes encode (source (nativeBytes saved)) (nativeBytes saved).length := by
  simp only [nativeBytes,List.length_map]
  apply congrArg List.ofFn
  funext i
  simp [copyHeap,put,copied,size,i.isLt]
 rw [point]
 exact source_bytes encode (nativeBytes saved)

#print axioms bytes
end NIJ_ReturnedWrite
