import RPz7_Op5T_OuterAccepted
set_option autoImplicit false
namespace AspisR1.Op5T_Schedule
open Aeneas Aeneas.Std Result S2W_Trace S2W_OuterOccurrences S2W_ExpandedTrace S2W_ExpandedChildren S2W_TraceSplice
theorem expanded_schedule {E : Type} {ops : AdapterRw.Ops} (port : ChildConeJoin E ops)
    (first : Op5T_Marks.FirstMarks port) (second : Op5T_Marks.SecondMarks port) (outer : Log)
    (good : Op5T_OuterAccepted.good ops outer) (shape : tags outer = [false,true]) :
    ∃ pre middle fs ss,
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss := by
  obtain ⟨pre,e1,rest,same,_,m1,remaining⟩ := split_tag outer false [true] shape
  obtain ⟨middle,e2,post,same2,_,m2,_⟩ := split_tag rest true [] remaining
  have member1 : e1 ∈ outer := by rw [same]; simp
  have member2 : e2 ∈ outer := by rw [same,same2]; simp
  obtain ⟨fs,layout1⟩ := first.source e1 m1 (good e1 member1 (by rw [m1]; decide))
  obtain ⟨ss,layout2⟩ := second.source e2 m2 (good e2 member2 (by rw [m2]; decide))
  let headLog := projected port pre ++ [.source none]
  let interval := projected port middle ++ [.source none]
  let ss' := {ss with afterFinish := ss.afterFinish ++ projected port post}
  refine ⟨headLog,interval,fs,ss',?_⟩
  have splice := S2W_ExpandedTrace.splice (children port) outer pre middle post e1 e2
    (by simp only [same,same2,List.append_assoc,List.cons_append,List.nil_append])
  unfold projected
  rw [splice]
  simp only [List.map_append,expand,children,invocation_first e1 m1,invocation_second e2 m2,
    List.map_cons,List.map_nil,project,layout1,layout2]
  simp only [headLog,interval,ss',S2W_SiteSchedule.timeline,S2W_SiteSchedule.secondTrace,
    projected,List.append_assoc,List.cons_append,List.nil_append]

#print axioms expanded_schedule
end AspisR1.Op5T_Schedule
