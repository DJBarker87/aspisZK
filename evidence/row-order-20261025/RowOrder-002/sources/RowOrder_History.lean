import S2W_D189Consolidation

/-! A consumer of the SAME SourceCuts exported by D189. The runtime history
is retained, including its key, ledger and events: no synthetic empty history,
hash injectivity or independently existential saved bytes are used. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RowOrder_History
open Aeneas Aeneas.Std Result S2Trust MultiproofConeCanonical
open S2W_D189Entry S2W_D189Wrappers S2W_NativeConsolidation
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_EntryWriteHistory
open S2W_AuthenticatedInputs S2W_TrustedStd
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Reindex the actual committed history without changing any runtime data.
Only the equality proved from the actual write changes its saved-byte index. -/
def reindex (written saved loaded : Bytes) (same : written = saved)
    (runtime : S2X.CheckpointVersionBinding written loaded) :
    S2X.CheckpointVersionBinding saved loaded where
  key := runtime.key
  ledger := runtime.ledger
  events := runtime.events
  savedAtCommit := runtime.savedAtCommit.trans same
  loadedAtEntry := runtime.loadedAtEntry
  noInterveningWrite := runtime.noInterveningWrite

/-- No history premise is discharged here. The local std copy and the SAME
writer result identify its committed bytes; the runtime's version binding and
P2Prime remain separate premises. SourceCuts must be D189's exported witness. -/
theorem on_d189_cuts {A : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (ops : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First)
    (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (program : S2W_ExtractionBoundary.Program) (data1 : Slice U8)
    (state1 final1 : A) (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
    (accepted1 : first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts ops e1.first (e2.second secondSizes) saved f s)
    (decode : HeaderDecode) (H : Bytes → State)
    (writer : CheckpointWriterConeJoin ops decode H f.semantic f.pub f.proof f.split)
    (reader : CheckpointReaderConeJoin ops decode H s.pub s.proof s.checkpoint)
    (runtime : S2X.CheckpointVersionBinding
      (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768)
      (bytesOf s.checkpoint.val))
    (p2prime : P2Prime H f.proof f.pub s.proof s.pub) :
    ∃ version : S2X.CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val),
      version.key = runtime.key ∧ version.ledger = runtime.ledger ∧
      version.events = runtime.events ∧
      bytesOf s.checkpoint.val = bytesOf saved.val ∧
      bytesOf s.proof.val = bytesOf f.proof.val ∧
      bytesOf s.pub.val = bytesOf f.pub.val ∧
      (bytesOf saved.val).length = 1768 := by
  obtain ⟨native,written⟩ := first_accepted native1 copy std allocator e1 program data1
    state1 final1 saved post1 accepted1
  have source1 : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program e1.first data1 =
      ok (.Ok saved) :=
    ((S2W_DigestExtraction.sourceBoundary ops native1 native2 hashv extraction).stage1
      program e1.first data1).symm.trans native
  have size := checkpoint_size e1 ops program data1 saved source1
  have copied : payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 =
      bytesOf saved.val := by
    rw [written, written_bytes encode e1.heap 2 0 0 (source (nativeBytes saved)) rfl rfl size]
    have savedSize : (nativeBytes saved).length = 1768 := by
      simpa only [nativeBytes,List.length_map] using writer.size saved cuts.first
    rw [← savedSize, source_bytes, vector_representation]
  let version := reindex _ _ _ copied runtime
  obtain ⟨proof,pub,checkpoint,length⟩ := authenticated_inputs ops decode H f.semantic
    f.pub f.proof s.pub s.proof s.checkpoint f.split saved cuts.first cuts.second
    writer reader ⟨version⟩ p2prime
  exact ⟨version,rfl,rfl,rfl,checkpoint,proof,pub,length⟩

#print axioms reindex
#print axioms on_d189_cuts
#print on_d189_cuts
end AspisR1.RowOrder_History
end
