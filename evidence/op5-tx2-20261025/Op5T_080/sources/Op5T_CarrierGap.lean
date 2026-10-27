import Op5T_Fixture
import Op5T_Final
import Op5I_BatchEventCounterexample
set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5T_CarrierGap
open Aeneas Aeneas.Std Result
open S2W_Trace S2W_ExpandedTrace S2W_ExpandedChildren S2W_TraceSplice
open Op5I_BatchEventCounterexample
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Op5I_AcceptedCarrierCounterexample (readEvents evaluated_reply)
theorem first_marks {E : Type} {ops : AdapterRw.Ops} (base : ChildConeJoin E ops)
    (read : E) (original : Op5T_Marks.FirstMarks base) : Op5T_Marks.FirstMarks (inject base read) := by
  constructor
  intro event marked accepted
  obtain ⟨s, layout⟩ := original.source event marked accepted
  let go := fun (list : List (S2W_SiteSchedule.Event (Option E))) => list.flatMap (projectedAtBatch read)
  refine ⟨⟨go s.beforeBatch, .source (some read) :: go s.beforeQuery,
    go s.beforeSave, go s.afterSave⟩, ?_⟩
  rw [events_injected, project_list, layout]
  simp [S2W_SiteSchedule.firstTrace, go, projectedAtBatch, List.append_assoc]

theorem second_marks {E : Type} {ops : AdapterRw.Ops} (base : ChildConeJoin E ops)
    (read : E) (original : Op5T_Marks.SecondMarks base) : Op5T_Marks.SecondMarks (inject base read) := by
  constructor
  intro event marked accepted
  obtain ⟨s, layout⟩ := original.source event marked accepted
  let go := fun (list : List (S2W_SiteSchedule.Event (Option E))) => list.flatMap (projectedAtBatch read)
  refine ⟨⟨go s.beforeResume, go s.beforeBatch, .source (some read) :: go s.beforeQuery,
    go s.beforeFinish, go s.afterFinish⟩, ?_⟩
  rw [events_injected, project_list, layout]
  simp [S2W_SiteSchedule.secondTrace, go, projectedAtBatch, List.append_assoc]


/-- The concrete two-slot installation and corrected marks STILL permit
Op5I's bad read in an arbitrary port. This is a checked contract countermodel,
not a bad native hash execution or a shipped multiproof vulnerability. -/
theorem countermodel {F : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (port : ChildConeJoin (Bytes × State) (Op5T_SamePair.dictionary adapter ops stage finish B std))
    (first : Op5T_Marks.FirstMarks port) (second : Op5T_Marks.SecondMarks port)
    (event : S2W_Trace.Event) (marked : S2W_OuterOccurrences.mark event = some false)
    (accepted : Op5T_Marks.accepted (Op5T_SamePair.dictionary adapter ops stage finish B std) event)
    (H : Bytes → State) (a : Bytes) (d : State) (bad : d ≠ H a) :
    ∃ fake : ChildConeJoin (Bytes × State) (Op5T_SamePair.dictionary adapter ops stage finish B std),
      Op5T_Marks.FirstMarks fake ∧ Op5T_Marks.SecondMarks fake ∧
      (∃ before after, events fake event = before ++ [.site .batch0,.child (a,d)] ++ after) ∧
      ∀ (R : Type) (code : Program Bytes State R),
        readEvents (events fake event) ≠ (eval H code).1 := by
  let fake := inject port (a,d)
  obtain ⟨segments,layout⟩ := first.source event marked accepted
  have projectedMember : S2W_SiteSchedule.Event.site .batch0 ∈ (events port event).map project := by
    rw [layout]
    simp [S2W_SiteSchedule.firstTrace]
  have batchMember : .site .batch0 ∈ events port event := by
    obtain ⟨chosen,belongs,same⟩ := List.mem_map.mp projectedMember
    cases chosen with
    | outer x => cases same
    | child x => cases same
    | site site =>
      have equal := S2W_SiteSchedule.Event.site.inj same
      subst site
      exact belongs
  obtain ⟨before,after,adjacent⟩ := batch_adjacent (a,d) (events port event) .batch0 (Or.inl rfl) batchMember
  have emitted : events fake event = before ++ [.site .batch0,.child (a,d)] ++ after := by
    rw [events_injected]
    exact adjacent
  refine ⟨fake,first_marks port (a,d) first,second_marks port (a,d) second,
    ⟨before,after,emitted⟩,?_⟩
  intro R code same
  have member : (a,d) ∈ readEvents (events fake event) := by
    rw [emitted]
    simp [readEvents,List.filterMap_append]
  rw [same] at member
  exact bad (evaluated_reply H code (a,d) member)

#print axioms first_marks
#print axioms second_marks
#print axioms countermodel
end AspisR1.Op5T_CarrierGap
end

-- One final audit of every new named theorem, not a package replay.
#print axioms AspisR1.Op5T_Accepted.accepted_pair_claims_op5
#print axioms AspisR1.Op5T_Claims.accepted_pair_claims
#print axioms AspisR1.Op5T_Concrete.stage_source
#print axioms AspisR1.Op5T_Concrete.current_source
#print axioms AspisR1.Op5T_Cuts.first_batch
#print axioms AspisR1.Op5T_Cuts.second_batch
#print axioms AspisR1.Op5T_D189.accepted_run
#print axioms AspisR1.Op5T_Final.accepted_pair_claims_op5
#print axioms AspisR1.Op5T_Fixture.success
#print axioms AspisR1.Op5T_Fixture.nonvacuity
#print axioms AspisR1.Op5T_Install.map_success_iff
#print axioms AspisR1.Op5T_Install.other_current
#print axioms AspisR1.Op5T_Install.other_stage
#print axioms AspisR1.Op5T_Install.tx1_slot
#print axioms AspisR1.Op5T_Install.tx2_slot
#print axioms AspisR1.Op5T_Marks.weaken_first
#print axioms AspisR1.Op5T_Marks.weaken_second
#print axioms AspisR1.Op5T_Marks.source_sites
#print axioms AspisR1.Op5T_Marks.accepted_source_marks
#print axioms AspisR1.Op5T_NativeAuth.accepted_batch
#print axioms AspisR1.Op5T_NativeSchedule.accepted_run
#print axioms AspisR1.Op5T_Op3.accepted_pair_claims_op3
#print axioms AspisR1.Op5T_OuterAccepted.first_good
#print axioms AspisR1.Op5T_OuterAccepted.second_good
#print axioms AspisR1.Op5T_P6.boundary
#print axioms AspisR1.Op5T_P6.no_fabricated_read
#print axioms AspisR1.Op5T_SamePair.batches
#print axioms AspisR1.Op5T_Schedule.expanded_schedule
#print axioms AspisR1.Op5T_Scheduled.accepted_run
#print axioms AspisR1.Op5T_SelectedPaths.indexed_paths
#print axioms AspisR1.Op5T_SuccessAccepted.accepted_pair_claims_op5
#print axioms AspisR1.Op5T_Tx2.accepted_pair_claims_tx2
