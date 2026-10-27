import CPP_ProgramErasure
import Hir_SelectedVersion
import Hir_SelectedJoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Selected
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_ProvenanceModel Hir_WriterSelect
open CPP_Invocation CPP_Oracle CPP_Schedule S2W_NativeConsolidation MultiproofConeCanonical
open S2W_EntryWriteHistory S2W_ReturnedCheckpoint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem version {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (law : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (initial : Store) (schedule : CPP_Schedule.Schedule A (Call A)) (writer : Writer A)
    (found : let out := CPP_Schedule.run n1 n2 copy allocator id H initial schedule
      search n1 copy allocator id (out.2.2.layout.handles 6).1
        (out.1 (out.2.2.layout.handles 6).1).data (calls n1 n2 copy allocator id H initial (erase schedule)) = some writer)
    (f : FirstCut) (s : SecondCut)
    (cuts : let out := CPP_Schedule.run n1 n2 copy allocator id H initial schedule
      SourceCuts (DrvC_Installation.sdk c) (load writer.site.before writer.site.call.layout).first
        ((load out.1 out.2.2.layout).second secondSizes) writer.saved f s) :
    Nonempty (S2X.CheckpointVersionBinding
      (payloadBytes encode (writer.post.payload ((load writer.site.before writer.site.call.layout).heap.accounts 2).1) 1768)
      (bytesOf s.checkpoint.val)) := by
  rw [CPP_RunErasure.exact] at found cuts
  exact Hir_SelectedVersion.on_cuts c law n1 n2 hashv extraction copy std allocator id H initial
    (erase schedule) writer found f s cuts

/-- Count-complete schedule preservation does not spend another collision
summand. The selected lifetime uses precisely the existing2965 envelope. -/
theorem one_loss {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (initial : Store)
    (schedule : CPP_Schedule.Schedule A (Call A)) (Q0 Q1 : Nat)
    (bound : ∀ H, (eval H (CPP_Schedule.program n1 copy allocator id c hashv initial schedule)).1.length ≤ Q0+Q1+1018)
    (project : Hir_LifetimeExperiment.Execution A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    lazyMean (Hir_SelectedJoint.program c hashv n1 copy allocator id initial (erase schedule) project) emptyTable
      (fun v => indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965) v)) ≤
      6*((Q0+Q1+2965 : Nat) : Rat)^2/(2:Rat)^256 := by
  apply Hir_SelectedJoint.one_loss c hashv n1 copy allocator id initial (erase schedule) Q0 Q1
  intro H
  rw [← CPP_ProgramErasure.exact]
  exact bound H

#print axioms version
#print axioms one_loss
end AspisR1.CPP_Selected
end
