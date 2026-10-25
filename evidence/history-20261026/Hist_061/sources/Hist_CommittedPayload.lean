import S2W_D189Wrappers
import S2W_DigestExtraction
import S2W_D189Entry
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_CommittedPayload
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_EntryWriteHistory
open MultiproofConeCanonical AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem copied {A : Type} (ops : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first native1 copy allocator e program data state = ok (.Ok (saved,post,final)))
    (savedSize : saved.val.length = 1768) :
    payloadBytes encode (post.payload (e.heap.accounts 2).1) 1768 = bytesOf saved.val := by
  obtain ⟨native,written⟩ := first_accepted native1 copy std allocator e program data state final saved post accepted
  have source : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program e.first data = ok (.Ok saved) :=
    (extraction.stage1 program e.first data).symm.trans native
  have size := checkpoint_size e ops program data saved source
  rw [written,written_bytes encode e.heap 2 0 0 (source (nativeBytes saved)) rfl rfl size]
  have nativeSize : (nativeBytes saved).length = 1768 := by
    simpa only [nativeBytes,List.length_map] using savedSize
  rw [← nativeSize,source_bytes,vector_representation]

/-- Reindex a DERIVED history to the computed committed payload, retaining
its actual key, ledger and event sequence. No history field is an input law. -/
def committed_version (written saved loaded : Bytes) (copied : written = saved)
    (version : S2X.CheckpointVersionBinding saved loaded) : S2X.CheckpointVersionBinding written loaded where
  key := version.key
  ledger := version.ledger
  events := version.events
  savedAtCommit := version.savedAtCommit.trans copied.symm
  loadedAtEntry := version.loadedAtEntry
  noInterveningWrite := version.noInterveningWrite

#print axioms copied
#print axioms committed_version
end AspisR1.Hist_CommittedPayload
end
