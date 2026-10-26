import PoolT_Child
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolT_SourceWrite
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory
open MultiproofConeCanonical Hist_Store Hist_RuntimeEntry

/-- A committed local canonical verifier writer action supplies its own actual
accepted native reply, actual key, original proof/public buffers, statement
and native verifier child, full copied bytes and1768 size. No independently
accepted child, output/copy observation or post-selected writer is assumed.
This remains the existing local writer-action interpretation; runtime genesis,
canonical-bank scheduling and loading are outside this theorem. -/
theorem verifier {A : Type} (ops : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (program : S2W_ExtractionBoundary.Program) (before after : Store) (layout : Layout)
    (data : Slice U8) (state : A) (key : Nat) (image : AspisV8R19.DuplexFrames.Bytes)
    (committed : Hiq_NativeWriter.apply native1 copy allocator program before layout data state =
      (after,.committedWrite key image)) :
    ∃ saved post final statement semantic proof split,
      first native1 copy allocator (load before layout) program data state = ok (.Ok (saved,post,final)) ∧
      key = (layout.handles 2).1 ∧ after = commit before key saved ∧
      saved.val.length = 1768 ∧ image = bytesOf saved.val ∧
      payloadBytes encode (post.payload key) 1768 = image ∧
      ops.op47 (before (layout.handles 1).1).data = ok (.Ok statement) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        statement = ok semantic ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        (before (layout.handles 0).1).data {start := 688#usize, «end» := 58295#usize} = ok proof ∧
      ops.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        semantic (before (layout.handles 1).1).data proof split () none = ok (.Ok saved) := by
  obtain ⟨saved,post,final,accepted,sameKey,sameImage,storeEq,bytes⟩ :=
    PoolT_Event.verifier native1 copy std allocator program before after layout data state key image committed
  have native := (first_accepted native1 copy std allocator (load before layout)
    program data state final saved post accepted).1
  have sourceAccepted := (extraction.stage1 program (load before layout).first data).symm.trans native
  have size := PoolT_Verifier.returned_size ops (load before layout) program data saved sourceAccepted
  obtain ⟨statement,semantic,proof,split,decode,getter,range,child⟩ :=
    PoolT_Child.original_inputs ops (load before layout) program data saved sourceAccepted
  refine ⟨saved,post,final,statement,semantic,proof,split,accepted,sameKey,?_,size,sameImage,?_,decode,getter,range,child⟩
  · simpa only [sameKey] using storeEq
  · simpa only [size,← sameKey] using bytes

#print axioms verifier
end AspisR1.PoolT_SourceWrite
end
