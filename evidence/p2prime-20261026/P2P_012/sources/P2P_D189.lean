import P2P_Scheduled
import SAP_Scheduled
import Op5T_Scheduled
import S2W_D189Consolidation
import S2W_D189Wrappers
import S2W_ScheduledConsolidation

/-! Full Required14 for every accepted two-transaction wrapper execution in
the D189 SDK/std/runtime interpretation. Primitive interpretation and owned
extraction are the existing trust items; no caller cut or account-frame
conclusion occurs in a premise. Child ports remain separately named. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.P2P_D189
open Aeneas Aeneas.Std Result S2Trust S2LeadInterface
open S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd S2W_WrapperLaws
open S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

open S2W_D189Consolidation
theorem accepted_run {W A E : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (ops : AdapterRw.Ops) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (port : ChildConeJoin E ops) (firstMarks : Op5T_Marks.FirstMarks port) (secondMarks : Op5T_Marks.SecondMarks port) :
    ∃ f s outer pre middle fs ss,
      P2P_Origin.Fact ops program (e2.second secondSizes) data2 slot s ∧
      SourceCuts ops e1.first (e2.second secondSizes) saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement=ok f.semantic ∧
      S2W_ExpandedTrace.runExpanded ops (children port)
        (S2W_Observation.two ops program e1.first data1 (e2.second secondSizes) data2 slot) [] =
        ok (.Ok saved,S2W_ExpandedTrace.full (children port) outer) ∧
      S2W_D189Interpretation.runOwned ops
        (S2W_Observation.two ops program e1.first data1 (e2.second secondSizes) data2 slot) [] e1.heap =
        ok (.Ok saved,outer,e1.heap) ∧
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss ∧
      post2 = e2.heap ∧
      before e1 e2 .tx1 = S2W_D189Interpretation.nativeObserve L encode e1.metadata 3 w1 e1.heap.ambient ∧
      before e1 e2 .tx2 = S2W_D189Interpretation.nativeObserve L encode e2.metadata 7 w2 e2.heap.ambient ∧
      ∀ (decode : HeaderDecode) (nodes : Nat → Nat → Slice U8) (y1 : Slice U8),
      CheckpointWriterConeJoin ops decode H f.semantic f.pub f.proof f.split →
      CheckpointReaderConeJoin ops decode H s.pub s.proof s.checkpoint →
      S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) →
      P2Prime H f.proof f.pub s.proof s.pub →
      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes →
      S2W_ChildJoins.S8StageConeJoin f.proof y1 →
      ∃ parsed,
        S2W_LeadInterface.S2CallerFacts
          (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1))
          (S2Z.Oracle.leadDigest ops) () H (bytesOf f.proof.val) (bytesOf f.pub.val)
          (bytesOf saved.val) parsed ∧
        (∀ site, (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1)).reached site ↔
          S2W_SiteSchedule.Event.site site ∈ projected port outer) := by
  obtain ⟨owned1,written⟩ := first_accepted native1 copy std allocator e1 program data1 state1 final1 saved post1 accepted1
  obtain ⟨owned2,unchanged⟩ := second_accepted native2 allocator e2 program data2 slot state2 final2 post2 accepted2
  let boundary := S2W_DigestExtraction.sourceBoundary ops native1 native2 hashv extraction
  have source1 : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program e1.first data1 = ok (.Ok saved) :=
    (boundary.stage1 program e1.first data1).symm.trans owned1
  obtain ⟨f,s,outer,pre,middle,fs,ss,origin,cuts,selected,execution,expanded,layout,projectedInputs⟩ :=
    P2P_Scheduled.accepted_run ops native1 native2 hashv extraction sha256 H p1 syscall
      program e1.first (e2.second secondSizes) data1 data2 slot saved owned1 owned2 port firstMarks secondMarks
  refine ⟨f,s,outer,pre,middle,fs,ss,origin,cuts,selected,expanded,
    S2W_D189Interpretation.accepted_owned_frame ops _ [] outer (core.result.Result.Ok saved : core.result.Result (alloc.vec.Vec U8) AdapterRw.Cuts.PE) e1.heap execution,
    layout,unchanged,?_,?_,?_⟩
  · exact (S2W_D189Interpretation.native_observation L sdk encode e1.metadata 3 w1 e1.heap
      admission1.related admission1.entry.valid).symm
  · exact (S2W_D189Interpretation.native_observation L sdk encode e2.metadata 7 w2 e2.heap
      admission2.related admission2.entry.valid).symm
  intro decode nodes y1 writer reader history p2prime entry multiproof scan
  have destinationSize := checkpoint_size e1 ops program data1 saved source1
  have versionAtWrite : S2X.CheckpointVersionBinding
      (payloadBytes encode ((writeBracket e1.heap 2 0 0 (source (nativeBytes saved))).payload
        (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) := by
    rw [← written]; exact history
  obtain ⟨_,⟨version⟩⟩ := returned_committed e1.heap 2 0 0 saved (bytesOf s.checkpoint.val)
    rfl rfl destinationSize (writer.size saved cuts.first) versionAtWrite
  obtain ⟨parsed,partialFacts,sites⟩ := projectedInputs decode nodes y1 writer reader version p2prime
    entry multiproof scan (before e1 e2) (after e1 e2 post1)
  have frames := wrapper_frames e1 e2 ops program data1 saved source1 post1 written
  refine ⟨parsed,?_,sites⟩
  apply (S2W_TwoFieldAudit.full_fields_iff _ ops H _ _ _ parsed partialFacts).2
  exact ⟨fun site _ a allowed => frames.1 site a allowed,fun _ => frames.2⟩

#print axioms accepted_run
end AspisR1.P2P_D189
end
