import SCH_OuterIdealLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_OuterTrace
open Aeneas Aeneas.Std Result GExq_OuterLower
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- One trace, produced by this ideal execution, with exact ordered reads. -/
theorem accepted {F C A : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (code : Native A) (value : A)
    (success : (eval H (SdkC_Oracle.program (lower (SCH_OuterIdealLog.child c hashv) code))).2 = ok value) :
    ∃ log,
      S2W_Trace.run (SCH_IdealSdk.dictionary c hashv H) code [] = ok (value,log) ∧
      (eval H (SdkC_Oracle.program (lower (SCH_OuterIdealLog.child c hashv) code))).1 =
        SCH_OuterIdealLog.trace c hashv H log := by
  obtain ⟨log,ran⟩ := SCH_TraceExists.accepted _ code value []
    ((SCH_Lower.result c hashv H code).symm.trans success)
  refine ⟨log,ran,?_⟩
  simpa only [SCH_OuterIdealLog.trace,List.flatMap_nil,List.nil_append] using
    (SCH_OuterIdealLog.flatten c hashv H code [] log value ran)

#print axioms accepted
end AspisR1.SCH_OuterTrace
end
