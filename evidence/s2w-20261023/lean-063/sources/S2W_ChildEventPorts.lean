import S2W_InputSchedule

/-! Fixed-invocation event ports: child trace carriers are source executions,
not independently selected lists. Child erasure and source-mark theorems are
separate per-child cone-join hypotheses, per D188. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_ChildEventPorts
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
abbrev ChildExecution (E A : Type) := Result (A × List (S2W_SiteSchedule.Event E))

def forget {E A : Type} (execution : ChildExecution E A) : Result A := do
  let result ← execution
  ok result.1

/-- First-entry source instrumentation is on THIS invocation and erases to
its exact extracted call, including errors/divergence. Mark positions are a
local child source theorem. No global Inputs, caller field or frame occurs. -/
structure FirstEntryEventConeJoin {E : Type} (ops : AdapterRw.Ops) (f : FirstCut)
    (execution : ChildExecution E (core.result.Result (alloc.vec.Vec U8) AdapterRw.Cuts.PE))
    (segments : S2W_SiteSchedule.FirstSegments E) : Prop where
  erasure : forget execution = AdapterRw.first_decoded ops f.semantic f.pub f.proof f.split
  sourceMarks : ∀ result log, execution = ok (result,log) → log = S2W_SiteSchedule.firstTrace segments

/-- Second-entry source instrumentation is independently indexed to its fixed
proof/public/checkpoint inputs and exact source op11. -/
structure SecondEntryEventConeJoin {E : Type} (ops : AdapterRw.Ops) (s : SecondCut)
    (execution : ChildExecution E (core.result.Result Unit AdapterRw.Cuts.PE))
    (segments : S2W_SiteSchedule.SecondSegments E) : Prop where
  erasure : forget execution = ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
    s.pub s.proof s.checkpoint () none
  sourceMarks : ∀ result log, execution = ok (result,log) → log = S2W_SiteSchedule.secondTrace segments

/-- Source success supplies the returning child event trace. An opaque returned
value alone is never used to invent events. The erasure premise is child-owned. -/
theorem returning_trace {E A : Type} (execution : ChildExecution E A) (out : A)
    (success : forget execution = ok out) : ∃ log, execution = ok (out,log) := by
  cases execution with
  | fail e => cases success
  | div => cases success
  | ok pair =>
    have value : pair.1 = out := Result.ok.inj success
    exact ⟨pair.2,by cases pair; simp_all⟩

/-- One derived fixed source cut pair plus the exact child event runs and the
12-field retained-input/schedule projection. Only the BEFORE/AFTER account
observations are left arbitrary; their two frame fields are not claimed. -/
theorem accepted_native_observed_inputs {E : Type}
    (ops : AdapterRw.Ops) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_ExtractionBoundary.AeneasExtraction ops native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (runtime : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 program accounts1 data1 = ok (.Ok saved))
    (accepted2 : native2 program accounts2 data2 slot = ok (.Ok ())) :
    ∃ f s, SourceCuts ops accounts1 accounts2 saved f s ∧
      ∀ (decode : HeaderDecode) (nodes : Nat → Nat → Slice U8) (y1 : Slice U8),
      CheckpointWriterConeJoin ops decode H f.semantic f.pub f.proof f.split →
      CheckpointReaderConeJoin ops decode H s.pub s.proof s.checkpoint →
      CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val) →
      P2Prime H f.proof f.pub s.proof s.pub →
      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes →
      S2W_ChildJoins.S8StageConeJoin f.proof y1 →
      ∀ (firstExecution : ChildExecution E (core.result.Result (alloc.vec.Vec U8) AdapterRw.Cuts.PE))
        (secondExecution : ChildExecution E (core.result.Result Unit AdapterRw.Cuts.PE))
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
  obtain ⟨f,s,cuts⟩ := cuts_of_acceptance ops native1 native2 hashv extraction program accounts1 accounts2
    data1 data2 slot saved accepted1 accepted2
  refine ⟨f,s,cuts,?_⟩
  intro decode nodes y1 writer reader version p2prime entry multiproof scan
    firstExecution secondExecution fs ss firstPort secondPort pre middle before after
  obtain ⟨firstEvents,firstRun⟩ := returning_trace firstExecution (.Ok saved)
    (firstPort.erasure.trans cuts.first)
  obtain ⟨secondEvents,secondRun⟩ := returning_trace secondExecution (.Ok ())
    (secondPort.erasure.trans cuts.second)
  obtain ⟨parsed,facts⟩ := input_schedule ops H accounts1 accounts2 f s saved cuts decode nodes y1
    writer reader version p2prime entry multiproof scan
    (S2W_ExtractionBoundary.native_oracle ops native1 native2 hashv extraction sha256 H p1 runtime)
    pre middle fs ss before after
  refine ⟨parsed,firstEvents,secondEvents,firstRun,secondRun,facts,?_⟩
  rw [firstPort.sourceMarks _ _ firstRun,secondPort.sourceMarks _ _ secondRun]
  rfl

#print axioms returning_trace
#print axioms accepted_native_observed_inputs
#print FirstEntryEventConeJoin
#print SecondEntryEventConeJoin
end AspisR1.S2W_ChildEventPorts
end
