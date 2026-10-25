import SdkD_Marks
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_Nonvacuity

/-- The new child and both accepted-only laws are inhabited for EVERY installed
dictionary. They impose no new restriction on the old accepted executions. -/
theorem instance_exists {F : Type} (adapter : AdapterRw.Ops) (current : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    ∃ port : S2W_ExpandedChildren.ChildConeJoin Unit
      (ClaimsUnrolledSdk.sdkOps (Tx2I_Install.install adapter stage finish) current B std),
      Op5T_Marks.FirstMarks port ∧ Op5T_Marks.SecondMarks port :=
  ⟨SdkD_Child.port adapter current stage finish B std,
    SdkD_Marks.first adapter current stage finish B std,
    SdkD_Marks.second adapter current stage finish B std⟩

#print axioms instance_exists
end AspisR1.SdkD_Nonvacuity
end
