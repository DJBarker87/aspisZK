import CPP_AtomicBatchSuffix
import Hir_SelectedVersion
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicVersion
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_AtomicSchedule Hir_ProvenanceModel Hir_WriterSelect
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory S2W_ReturnedCheckpoint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem on_cuts {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (law : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (initial : Store) (schedule : Schedule A (Call A)) (writer : Writer A)
    (found : let out := run native1 native2 copy allocator id H initial schedule
      search native1 copy allocator id (out.2.2.layout.handles 6).1
        (out.1 (out.2.2.layout.handles 6).1).data (sites native1 native2 copy allocator id H initial schedule) = some writer)
    (f : FirstCut) (s : SecondCut)
    (cuts : let out := run native1 native2 copy allocator id H initial schedule
      SourceCuts (DrvC_Installation.sdk c) (load writer.site.before writer.site.call.layout).first
        ((load out.1 out.2.2.layout).second secondSizes) writer.saved f s) :
    Nonempty (S2X.CheckpointVersionBinding
      (payloadBytes encode (writer.post.payload ((load writer.site.before writer.site.call.layout).heap.accounts 2).1) 1768)
      (bytesOf s.checkpoint.val)) := by
  let out := run native1 native2 copy allocator id H initial schedule
  obtain ⟨member,birth,accepted1,dataEq⟩ := Hir_Search.sound native1 copy allocator id _ _ _ writer found
  obtain ⟨saved,post,final,front,events,accepted,dataEq',trace,history⟩ :=
    CPP_AtomicBatchSuffix.suffix (DrvC_Installation.sdk c) law native1 native2
      (fun id accounts data => (extraction.stage1 id accounts data).symm) copy std allocator
      id H initial schedule writer.site _ _ member birth
  have same := core.result.Result.Ok.inj (Result.ok.inj (accepted.symm.trans accepted1))
  have savedEq : saved = writer.saved := congrArg Prod.fst same
  rw [savedEq] at trace
  have sameKey := birth.2.1
  have trace' : Trace (DrvC_Installation.sdk c) id
      (commit writer.site.before (writer.site.call.layout.handles 2).1 writer.saved) events out.1 := by
    rw [sameKey]
    exact trace
  have n1 := (first_accepted native1 copy std allocator _ id writer.site.call.data writer.site.call.state
    writer.final writer.saved writer.post accepted1).1
  have source1 := (extraction.stage1 id _ writer.site.call.data).symm.trans n1
  have shape := Hiq_FirstShape.source c id _ writer.site.call.data writer.saved source1
  let version := Hiq_CausalVersion.version (DrvC_Installation.sdk c) law id writer.site.before out.1
    writer.site.call.layout out.2.2.layout writer.site.call.data writer.saved source1 events trace' sameKey.symm shape.1 f s cuts
  have copied := Hist_CommittedPayload.copied (DrvC_Installation.sdk c) native1 native2 hashv extraction
    copy std allocator (load writer.site.before writer.site.call.layout) id writer.site.call.data writer.site.call.state
    writer.final writer.saved writer.post accepted1 shape.2
  exact ⟨Hist_CommittedPayload.committed_version _ _ _ copied version⟩

#print axioms on_cuts
end AspisR1.CPP_AtomicVersion
end
