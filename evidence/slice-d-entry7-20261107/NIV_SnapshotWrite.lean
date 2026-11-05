import NIV_SnapshotSequence
import NIS_NativeSdkRelease
import NIS_ReturnedWrite
set_option autoImplicit false
namespace AspisR1.NIV_SnapshotWrite
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_TrustedStd
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_EntryWriteHistory

/-- Exact exclusive acquire/read/write/drop operation history. The source
payload is a fixed substage input; no parent output is assumed. -/
def History {W : Type} (L : Library W (Nat → Record)) (e : Entry)
    (w final : W) (src : Payload) : Prop :=
  ∃ token owner acquired read written,
    L.run w (.exclusive 2 token owner) = (acquired,.guard token) ∧
    L.run acquired (.deref token) =
      (read,.payload (e.heap.payload (e.heap.accounts 2).1)) ∧
    NIJ_NativeSdkCopy.Writes L (NIJ_ExclusiveRelease.guard e.heap 2 token owner)
      src.contents 0 (e.heap.payload (e.heap.accounts 2).1).descriptor.length read written ∧
    L.run written (.drop token) = (final,.unit)

/-- Complete value-producing snapshot history followed by the SAME exclusive
write history. This applies the named SDK and admission1 contracts. It does
not certify the native wrapper's ABI or allocator/cleanup realization. -/
theorem sequence_write {W : Type} (L : Library W (Nat → Record))
    (sdk : S2TrustedSdkBorrow L) (e : Entry) (w : W)
    (admission : S2W_D189Consolidation.RuntimeEntrypointAdmission L e w 3)
    (src : Payload) :
    ∃ middle final,
      NIV_SnapshotSequence.Sequence L e w NIV_SnapshotSequence.firstSpecs e.first.val middle ∧
      History L e middle final src ∧
      L.related final (copyHeap e.heap (e.heap.accounts 2).1 src) := by
  obtain ⟨middle,produced,restored⟩ := NIV_SnapshotSequence.first L sdk e w admission
  obtain ⟨token,owner,acquired,read,written,final,entered,viewed,copied,dropped,related⟩ :=
    NIJ_NativeSdkRelease.source L sdk e middle 2 src restored admission.entry.valid
  exact ⟨middle,final,produced,⟨token,owner,acquired,read,written,entered,viewed,copied,dropped⟩,related⟩

/-- Copy length is an explicit substage domain, to be established from the
actual returned checkpoint at the native boundary. Complete bytes are a
conclusion, not a saved-output equation supplied by the caller. -/
theorem returned_bytes {W : Type} (L : Library W (Nat → Record))
    (sdk : S2TrustedSdkBorrow L) (e : Entry) (w : W)
    (admission : S2W_D189Consolidation.RuntimeEntrypointAdmission L e w 3)
    (saved : alloc.vec.Vec U8)
    (size : (e.heap.payload (e.heap.accounts 2).1).descriptor.length = saved.val.length) :
    ∃ middle final,
      NIV_SnapshotSequence.Sequence L e w NIV_SnapshotSequence.firstSpecs e.first.val middle ∧
      History L e middle final (source (nativeBytes saved)) ∧
      L.related final (copyHeap e.heap (e.heap.accounts 2).1 (source (nativeBytes saved))) ∧
      payloadBytes encode
        ((copyHeap e.heap (e.heap.accounts 2).1 (source (nativeBytes saved))).payload
          (e.heap.accounts 2).1) saved.val.length = MultiproofConeCanonical.bytesOf saved.val := by
  obtain ⟨middle,final,produced,history,related⟩ :=
    sequence_write L sdk e w admission (source (nativeBytes saved))
  exact ⟨middle,final,produced,history,related,NIJ_ReturnedWrite.bytes e 2 saved size⟩

#print axioms sequence_write
#print axioms returned_bytes
end AspisR1.NIV_SnapshotWrite
