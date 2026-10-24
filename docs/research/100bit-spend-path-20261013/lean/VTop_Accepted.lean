import ChildJoin_Accepted
import ChildJoin_Decoder
import VTop_Checkpoint

/-! Full Required14 for every accepted two-transaction wrapper execution in
the D189 SDK/std/runtime interpretation. Primitive interpretation and owned
extraction are the existing trust items; no caller cut or account-frame
conclusion occurs in a premise. Child ports remain separately named. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_Accepted
open Aeneas Aeneas.Std Result S2Trust S2LeadInterface
open S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd S2W_WrapperLaws
open S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

open S2W_D189Consolidation ChildJoin_Decoder
theorem accepted_run {W A E : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (VTop_Entry.install adapter stage) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (reserved : Bool)
    (checkpointSource : VTop_Checkpoint.CheckpointSourceJoin stage
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (VTop_Entry.install adapter stage)) () reserved)
    (checkpointOracle : CheckpointBytes5Inputs.Oracle
      (VTop_Checkpoint.digest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (VTop_Entry.install adapter stage))) () H)
    (port : ChildConeJoin E (VTop_Entry.install adapter stage)) (firstMarks : FirstMarks port) (secondMarks : SecondMarks port) :
    ∃ f s outer pre middle fs ss,
      SourceCuts (VTop_Entry.install adapter stage) e1.first (e2.second secondSizes) saved f s ∧
      S2W_ExpandedTrace.runExpanded (VTop_Entry.install adapter stage) (children port)
        (S2W_Observation.two (VTop_Entry.install adapter stage) program e1.first data1 (e2.second secondSizes) data2 slot) [] =
        ok (.Ok saved,S2W_ExpandedTrace.full (children port) outer) ∧
      S2W_D189Interpretation.runOwned (VTop_Entry.install adapter stage)
        (S2W_Observation.two (VTop_Entry.install adapter stage) program e1.first data1 (e2.second secondSizes) data2 slot) [] e1.heap =
        ok (.Ok saved,outer,e1.heap) ∧
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss ∧
      post2 = e2.heap ∧
      before e1 e2 .tx1 = S2W_D189Interpretation.nativeObserve L encode e1.metadata 3 w1 e1.heap.ambient ∧
      before e1 e2 .tx2 = S2W_D189Interpretation.nativeObserve L encode e2.metadata 7 w2 e2.heap.ambient ∧
      ∀ (nodes : Nat → Nat → Slice U8) (y1 : Slice U8),
      VTop_Checkpoint.WriterProvenance stage
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (VTop_Entry.install adapter stage)) () f.semantic f.proof f.split →
      S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) →
      P2Prime H f.proof f.pub s.proof s.pub →
      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes →
      S2W_ChildJoins.S8StageConeJoin f.proof y1 →
      ∃ parsed,
        S2W_LeadInterface.S2CallerFacts
          (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1))
          (S2Z.Oracle.leadDigest (VTop_Entry.install adapter stage)) () H (bytesOf f.proof.val) (bytesOf f.pub.val)
          (bytesOf saved.val) parsed ∧
        (∀ site, (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1)).reached site ↔
          S2W_SiteSchedule.Event.site site ∈ projected port outer) := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,cuts,expanded,owned,layout,unchanged,firstBefore,secondBefore,continuation⟩ :=
    ChildJoin_Accepted.accepted_run L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      (VTop_Entry.install adapter stage) native1 native2 hashv extraction sha256 H p1 syscall
      program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2
      port firstMarks secondMarks
  refine ⟨f,s,outer,pre,middle,fs,ss,cuts,expanded,owned,layout,unchanged,firstBefore,secondBefore,?_⟩
  intro nodes y1 provenance history p2prime entry multiproof scan
  exact continuation nodes y1
    (VTop_Checkpoint.writer_join adapter stage H f.semantic f.pub f.proof f.split reserved
      checkpointSource checkpointOracle provenance)
    (VTop_Checkpoint.reader_join adapter stage H s.pub s.proof s.checkpoint reserved
      checkpointSource checkpointOracle)
    history p2prime entry multiproof scan

#print axioms accepted_run
#print accepted_run
end AspisR1.VTop_Accepted
end
