import S2W_DigestExtraction

/-! Continuation-4 consolidated PARTIAL result. One accepted native pair,
source-derived cuts, one typed ordered outer trace, exact traced child source
executions and twelve fields on their retained-input/schedule projection.
The two actual native account-frame fields remain unproved. Neither they nor
a whole-caller certificate occur as assumptions in accepted_run. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_D188Consolidation
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule S2W_ChildEventPorts

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
    (accepted2 : native2 program accounts2 data2 slot = ok (.Ok ())) :
    ∃ f s firstLog finalLog suffix,
      SourceCuts ops accounts1 accounts2 saved f s ∧
      S2W_Trace.run ops (S2W_Outer.stage1_owned ops S2W_Outer.traceEffects program accounts1 data1)
        [] = ok (.Ok saved,firstLog) ∧
      S2W_Trace.run ops (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program accounts2 data2 slot)
        firstLog = ok (.Ok (),finalLog) ∧
      S2W_Trace.run ops (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok saved,finalLog) ∧
      finalLog = firstLog ++ suffix ∧
      (∀ event ∈ finalLog, S2W_TraceFacts.ValidEvent ops event) ∧
      ∀ (decode : HeaderDecode) (nodes : Nat → Nat → Slice U8) (y1 : Slice U8),
      CheckpointWriterConeJoin ops decode H f.semantic f.pub f.proof f.split →
      CheckpointReaderConeJoin ops decode H s.pub s.proof s.checkpoint →
      CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val) →
      P2Prime H f.proof f.pub s.proof s.pub →
      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes →
      S2W_ChildJoins.S8StageConeJoin f.proof y1 →
      ∀ (firstExecution : ChildExecution E (core.result.Result (alloc.vec.Vec U8) AdapterRw.Cuts.PE))
        (secondExecution : ChildExecution E (core.result.Result Unit AdapterRw.aspis_r1_cost_probe.verifier.Error))
        (fs : S2W_SiteSchedule.FirstSegments E) (ss : S2W_SiteSchedule.SecondSegments E),
      FirstEntryEventConeJoin ops f firstExecution fs →
      SecondEntryEventConeJoin ops s secondExecution ss →
      ∀ (pre middle : List (S2W_SiteSchedule.Event E))
        (before after : S2LeadInterface.Site → Nat → S2LeadInterface.Account),
      ∃ parsed firstEvents secondEvents,
        firstExecution = ok (.Ok saved,firstEvents) ∧
        secondExecution = ok (.Ok (),secondEvents) ∧
        InputScheduleFacts (observation f s saved nodes y1 pre middle fs ss before after)
          ops H (bytesOf f.proof.val) (bytesOf f.pub.val) (bytesOf saved.val) parsed ∧
        pre ++ [.site .tx1] ++ firstEvents ++ middle ++ [.site .tx2] ++ secondEvents =
          S2W_SiteSchedule.timeline pre middle fs ss := by
  let boundary := S2W_DigestExtraction.sourceBoundary ops native1 native2 hashv extraction
  obtain ⟨f,s,cuts,project⟩ := S2W_ChildEventPorts.accepted_native_observed_inputs (E := E)
    ops native1 native2 hashv boundary sha256 H p1 runtime program accounts1 accounts2
    data1 data2 slot saved accepted1 accepted2
  obtain ⟨firstLog,finalLog,suffix,first,second,both,extension,valid⟩ :=
    S2W_ExtractionBoundary.accepted_native_observation ops native1 native2 hashv boundary
      program accounts1 accounts2 data1 data2 slot saved accepted1 accepted2
  exact ⟨f,s,firstLog,finalLog,suffix,cuts,first,second,both,extension,valid,project⟩

#print axioms accepted_run
#print axioms S2W_DigestExtraction.digest_eq_hashv
#print axioms S2W_DigestExtraction.native_binding
#print axioms S2W_AuthenticatedInputs.authenticated_inputs
#print axioms S2W_AuthenticatedInputs.authenticated_geometry
#print axioms S2W_SiteSchedule.located
#print axioms S2W_SiteSchedule.reached
#print axioms S2W_SiteSchedule.ordered
#print axioms S2W_SiteSchedule.source_schedule
#print axioms S2W_ChildEventPorts.returning_trace
#print axioms S2W_TwoFieldAudit.full_fields_iff
#print axioms S2W_TwoFieldAudit.changed_metadata_excludes_facts
#print accepted_run
#print S2W_DigestExtraction.AeneasExtraction
#print S2W_ExtractionBoundary.P1
#print S2W_ExtractionBoundary.RuntimeSyscall
#print S2W_AuthenticatedInputs.P2Prime
#print S2W_AuthenticatedInputs.CheckpointVersionBinding
#print S2W_AuthenticatedInputs.CheckpointWriterConeJoin
#print S2W_AuthenticatedInputs.CheckpointReaderConeJoin
#print S2W_ChildEventPorts.FirstEntryEventConeJoin
#print S2W_ChildEventPorts.SecondEntryEventConeJoin
#print S2W_ChildJoins.FirstEntryVerifierConeJoin
#print S2W_ChildJoins.MultiproofConeJoin
#print S2W_ChildJoins.S8StageConeJoin
end AspisR1.S2W_D188Consolidation
end
