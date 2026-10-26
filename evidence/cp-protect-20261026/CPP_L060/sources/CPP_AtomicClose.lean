import CPP_AtomicVersion
import CPP_FullResult
import T2R_FullResult
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicClose
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_ProvenanceModel Hir_WriterSelect
open CPP_Invocation CPP_Oracle CPP_AtomicSchedule S2W_NativeConsolidation MultiproofConeCanonical
open S2W_EntryWriteHistory S2W_ReturnedCheckpoint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem closed {W A F C : Type} (L : Library W (Nat → Record)) (w1 w2 : W)
    (c : DrvC_Installation.Configuration F C)
    (law : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (initial : Store) (schedule : CPP_AtomicSchedule.Schedule A (Call A)) (writer : Writer A)
    (found : let out := CPP_AtomicSchedule.run n1 n2 copy allocator id H initial schedule
      search n1 copy allocator id (out.2.2.layout.handles 6).1
        (out.1 (out.2.2.layout.handles 6).1).data (sites n1 n2 copy allocator id H initial schedule) = some writer)
    (post2 : Heap (Nat → Record))
    (driver : OraclePortStoredExperimentC4.Input → Program Bytes State Bool)
    (prior : Program Bytes State Unit)
    (original : let out := CPP_AtomicSchedule.run n1 n2 copy allocator id H initial schedule
      T2R_FullResult.Outcome L (load writer.site.before writer.site.call.layout) (load out.1 out.2.2.layout) w1 w2
        c.adapter c.currentBase c.reserved c.query c.geometry c.stageBase c.finish c.boundaries c.std id
        writer.site.call.data out.2.2.data out.2.2.slot writer.saved writer.post post2 H driver prior) :
    let out := CPP_AtomicSchedule.run n1 n2 copy allocator id H initial schedule
    CPP_FullResult.Outcome L (load writer.site.before writer.site.call.layout) (load out.1 out.2.2.layout) w1 w2
      c.adapter c.currentBase c.reserved c.query c.geometry c.stageBase c.finish c.boundaries c.std id
      writer.site.call.data out.2.2.data out.2.2.slot writer.saved writer.post post2 H driver prior := by
  dsimp only at original ⊢
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,base,publicFacts,parser,acceptance,caller⟩ := original
  obtain ⟨version⟩ := CPP_AtomicVersion.on_cuts c law n1 n2 hashv extraction copy std allocator id H
    initial schedule writer found f s base.1
  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,base,publicFacts,parser,?_,?_⟩
  · obtain ⟨i,pub,proof,tag,size,fit,accepted⟩ := acceptance
    exact ⟨i,pub,proof,tag,size,fit,fun p2prime => accepted version p2prime⟩
  · exact caller version

#print axioms closed
end AspisR1.CPP_AtomicClose
end
