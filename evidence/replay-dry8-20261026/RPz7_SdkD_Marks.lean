import RPz7_SdkD_Child
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_Marks
open Aeneas Aeneas.Std Result
open S2W_ExpandedChildren S2W_TraceSplice

theorem first {F : Type} (adapter : AdapterRw.Ops) (current : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    Op5T_Marks.FirstMarks (SdkD_Child.port adapter current stage finish B std) := by
  constructor
  intro event marked success
  cases event with
  | returned call value =>
    cases call <;> simp_all only [S2W_OuterOccurrences.mark,Op5T_Marks.accepted,
      Option.some.injEq,reduceCtorEq]
    obtain ⟨saved,success⟩ := success
    have actual := SdkD_FirstChild.accepted
      (RowShape_InstalledSlots.verifierOps current B std) _ _ _ _ _ _ _ saved success
    exact ⟨⟨[],[],[],[]⟩,by
      simp only [events,SdkD_Child.port,SdkD_Child.execute,actual,SdkD_Child.expand,
        List.map_cons,List.map_nil,project,S2W_SiteSchedule.firstTrace,List.nil_append,
        List.cons_append]⟩

theorem second {F : Type} (adapter : AdapterRw.Ops) (current : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    Op5T_Marks.SecondMarks (SdkD_Child.port adapter current stage finish B std) := by
  constructor
  intro event marked success
  cases event with
  | returned call value =>
    cases call <;> simp_all only [S2W_OuterOccurrences.mark,Op5T_Marks.accepted,
      Option.some.injEq,reduceCtorEq]
    have actual := SdkD_Second.accepted (Tx2I_Install.stage stage finish) _ _ _ _ _ _ success
    exact ⟨⟨[],[],[],[],[]⟩,by
      simp only [events,SdkD_Child.port,SdkD_Child.execute,actual,SdkD_Child.expand,
        List.map_cons,List.map_nil,project,S2W_SiteSchedule.secondTrace,List.nil_append,
        List.cons_append]⟩

#print axioms first
#print axioms second
end AspisR1.SdkD_Marks
end
