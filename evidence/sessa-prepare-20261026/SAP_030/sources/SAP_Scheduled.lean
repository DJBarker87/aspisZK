import RawJ_RecordCuts
import Op5T_NativeSchedule
import S2W_ScheduledConsolidation
import S2W_NativeSchedule
import S2W_ReturnedCheckpoint

/-! Consolidation on the actual expanded source schedule. Twelve fields only:
account observations still require the native wrapper source/heap port. No
logical commit post-state is substituted for a native observed account. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_Scheduled
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice

theorem accepted_run {E : Type}
    (ops : AdapterRw.Ops) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (runtime : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 program accounts1 data1 = ok (.Ok saved))
    (accepted2 : native2 program accounts2 data2 slot = ok (.Ok ()))
    (port : ChildConeJoin E ops) (firstMarks : Op5T_Marks.FirstMarks port) (secondMarks : Op5T_Marks.SecondMarks port) :
    ∃ f s outer pre middle fs ss,
      SourceCuts ops accounts1 accounts2 saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement=ok f.semantic ∧
      S2W_Trace.run ops (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok saved,outer) ∧
      S2W_ExpandedTrace.runExpanded ops (children port)
        (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok saved,S2W_ExpandedTrace.full (children port) outer) ∧
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss ∧
      ∀ (decode : HeaderDecode) (nodes : Nat → Nat → Slice U8) (y1 : Slice U8),
      CheckpointWriterConeJoin ops decode H f.semantic f.pub f.proof f.split →
      CheckpointReaderConeJoin ops decode H s.pub s.proof s.checkpoint →
      CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val) →
      P2Prime H f.proof f.pub s.proof s.pub →
      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes →
      S2W_ChildJoins.S8StageConeJoin f.proof y1 →
      ∀ (before after : S2LeadInterface.Site → Nat → S2LeadInterface.Account),
      ∃ parsed,
        InputScheduleFacts (observation f s saved nodes y1 pre middle fs ss before after)
          ops H (bytesOf f.proof.val) (bytesOf f.pub.val) (bytesOf saved.val) parsed ∧
        (∀ site, (observation f s saved nodes y1 pre middle fs ss before after).reached site ↔
          S2W_SiteSchedule.Event.site site ∈ projected port outer) := by
  let boundary := S2W_DigestExtraction.sourceBoundary ops native1 native2 hashv extraction
  obtain ⟨f,s,rawLog,cuts,recorded,rawRun⟩ := RawJ_RecordCuts.native ops native1 native2 hashv extraction
    program accounts1 accounts2 data1 data2 slot saved accepted1 accepted2
  obtain ⟨outer,pre,middle,fs,ss,execution,expanded,_,layout,_,_,_⟩ :=
    Op5T_NativeSchedule.accepted_run ops native1 native2 hashv extraction program accounts1 accounts2
      data1 data2 slot saved accepted1 accepted2 port firstMarks secondMarks
  refine ⟨f,s,outer,pre,middle,fs,ss,cuts,recorded.1,execution,expanded,layout,?_⟩
  intro decode nodes y1 writer reader version p2prime entry multiproof scan before after
  obtain ⟨parsed,facts⟩ := input_schedule ops H accounts1 accounts2 f s saved cuts decode nodes y1
    writer reader version p2prime entry multiproof scan
    (S2W_DigestExtraction.native_oracle ops native1 native2 hashv extraction sha256 H p1 runtime)
    pre middle fs ss before after
  exact ⟨parsed,facts,fun site => by rw [layout]; rfl⟩

#print axioms accepted_run
end AspisR1.SAP_Scheduled
end
