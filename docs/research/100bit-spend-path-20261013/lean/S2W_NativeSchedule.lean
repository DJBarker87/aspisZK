import S2W_TraceSplice

/-! Accepted native source schedule on the expanded actual outer execution.
Only the named child erasure/source-mark theorems supply internal events. -/
set_option autoImplicit false
namespace AspisR1.S2W_NativeSchedule
open Aeneas Aeneas.Std Result S2W_Trace S2W_OuterOccurrences S2W_ExpandedTrace S2W_ExpandedChildren S2W_TraceSplice

theorem accepted_run {E : Type}
    (ops : AdapterRw.Ops) (native1 : S2W_ExtractionBoundary.First)
    (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (program : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 program accounts1 data1 = ok (.Ok saved))
    (accepted2 : native2 program accounts2 data2 slot = ok (.Ok ()))
    (port : ChildConeJoin E ops) (firstMarks : FirstMarks port) (secondMarks : SecondMarks port) :
    ∃ outer pre middle fs ss,
      run ops (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok saved,outer) ∧
      runExpanded ops (children port)
        (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok saved,full (children port) outer) ∧
      tags outer = [false,true] ∧
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss ∧
      (∀ a b : S2LeadInterface.Site, a.rank < b.rank →
        S2W_SiteSchedule.Event.site b ∈ projected port outer →
        S2W_SiteSchedule.Event.site a ∈ projected port outer) ∧
      (∀ a b : S2LeadInterface.Site, a.rank < b.rank →
        S2W_SiteSchedule.Event.site a ∈ projected port outer →
        S2W_SiteSchedule.Event.site b ∈ projected port outer →
        S2W_SiteSchedule.clock pre middle fs ss a < S2W_SiteSchedule.clock pre middle fs ss b) ∧
      (∀ a, projected port outer = S2W_SiteSchedule.before pre middle fs ss a ++
        [.site a] ++ S2W_SiteSchedule.after middle fs ss a) := by
  let boundary := S2W_DigestExtraction.sourceBoundary ops native1 native2 hashv extraction
  obtain ⟨firstLog,outer,_,firstRun,secondRun,execution,_,_⟩ :=
    S2W_ExtractionBoundary.accepted_native_observation ops native1 native2 hashv boundary
      program accounts1 accounts2 data1 data2 slot saved accepted1 accepted2
  have secondOwned : AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts2 data2 slot =
      ok (.Ok ()) := (boundary.stage2 program accounts2 data2 slot).symm.trans accepted2
  obtain ⟨secondLog,secondEmpty⟩ := S2W_TraceFacts.success_exists ops
    (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program accounts2 data2 slot) [] (.Ok ())
    ((S2W_OuterErasure.stage2_erasure ops program accounts2 data2 slot).trans secondOwned)
  have shifted := run_shift ops
    (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program accounts2 data2 slot) firstLog []
  rw [List.append_nil,secondEmpty] at shifted
  have joined : outer = firstLog ++ secondLog :=
    congrArg Prod.snd (Result.ok.inj (secondRun.symm.trans shifted))
  have shape : tags outer = [false,true] := by
    rw [joined]
    change (firstLog ++ secondLog).filterMap mark = _
    rw [List.filterMap_append]
    change tags firstLog ++ tags secondLog = _
    rw [S2W_FirstOccurrence.first_occurrence ops program accounts1 data1 saved firstLog firstRun,
      second_occurrence ops program accounts2 data2 slot secondLog secondEmpty]
    rfl
  obtain ⟨pre,middle,fs,ss,layout⟩ := expanded_schedule port firstMarks secondMarks outer shape
  refine ⟨outer,pre,middle,fs,ss,execution,execution_flatMap ops (children port) _ [] outer _ execution,
    shape,layout,?_,?_,?_⟩
  · intro a b _ _
    rw [layout]
    exact S2W_SiteSchedule.reached pre middle fs ss a
  · intro a b order _ _
    exact S2W_SiteSchedule.ordered pre middle fs ss a b order
  · intro a
    exact layout.trans (S2W_SiteSchedule.located pre middle fs ss a)

#print axioms accepted_run
#print accepted_run
end AspisR1.S2W_NativeSchedule
