import Uni_SecondMarks
set_option autoImplicit false
noncomputable section
namespace AspisR1.Uni_RejectedSecond
open Aeneas Aeneas.Std Result

def empty : Slice U8 := ⟨[],by decide⟩

theorem shape_rejects : Tx2I_Install.shape empty = ok (.Err .Parse) := by rfl

/-- Literal installed source shape rejects before resume or any suffix site. -/
theorem rejected_source {F Hash : Type} (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub checkpoint : Slice U8) :
    VTop_Trace.run (Tx2I_Install.stage base finish)
      (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub empty checkpoint hash none) [] =
        ok (.Err .Parse,[.returned (.op3 empty) (.Err .Parse)]) := by
  simp only [VTop_Flow.tx2_authenticated,VTop_Flow.traceEffects,Bind.bind,
    VTop_Trace.bind,VTop_Trace.perform,VTop_Trace.run,VTop_Trace.invoke,
    Tx2I_Install.stage,shape_rejects,VTop_Trace.thenResult,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    VTop_Trace.liftResult]
  rfl

theorem second_marks_force_resume {E : Type} {ops : AdapterRw.Ops}
    (port : S2W_ExpandedChildren.ChildConeJoin E ops)
    (marks : S2W_TraceSplice.SecondMarks port) (event : S2W_Trace.Event)
    (marked : S2W_OuterOccurrences.mark event = some true) :
    .resume ∈ Op5C_RejectedMarks.childSites (S2W_ExpandedChildren.events port event) := by
  obtain ⟨segments,layout⟩ := marks.source event marked
  have member : S2W_SiteSchedule.Event.site .resume ∈
      (S2W_ExpandedChildren.events port event).map S2W_TraceSplice.project := by
    rw [layout]
    simp [S2W_SiteSchedule.secondTrace]
  obtain ⟨chosen,belongs,same⟩ := List.mem_map.mp member
  cases chosen with
  | outer x => cases same
  | child x => cases same
  | site site =>
    have equal : site = .resume := S2W_SiteSchedule.Event.site.inj same
    subst site
    exact List.mem_filterMap.mpr ⟨.site .resume,belongs,rfl⟩

/-- Old SecondMarks cannot describe the faithful deployed shape-rejected trace.
This refutes the global instance; arbitrary fictional child logs still exist. -/
theorem no_global_second_mark_association {E : Type} {ops : AdapterRw.Ops}
    (event : S2W_Trace.Event) (marked : S2W_OuterOccurrences.mark event = some true) :
    ¬ ∃ port : S2W_ExpandedChildren.ChildConeJoin E ops,
      S2W_TraceSplice.SecondMarks port ∧
      Op5C_RejectedMarks.childSites (S2W_ExpandedChildren.events port event) =
        Uni_SecondMarks.sourceSites [.returned (.op3 empty) (.Err .Parse)] := by
  rintro ⟨port,marks,associated⟩
  have forced := second_marks_force_resume port marks event marked
  rw [associated] at forced
  exact List.not_mem_nil forced

#print axioms shape_rejects
#print axioms rejected_source
#print axioms second_marks_force_resume
#print axioms no_global_second_mark_association
end AspisR1.Uni_RejectedSecond
end
