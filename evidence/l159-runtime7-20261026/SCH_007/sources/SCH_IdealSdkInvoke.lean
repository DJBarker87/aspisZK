import SCH_IdealSdk
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_IdealSdkInvoke
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCH_IdealSdk
attribute [local irreducible] GExq_ChildCode.execute SCH_IdealSdk.dictionary

theorem invoke {F C A : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (call : S2W_Trace.Call A) :
    S2W_Trace.invoke (SCH_IdealSdk.dictionary c hashv H) call =
      (eval H (SdkC_Oracle.program (GExq_ChildCode.execute c.adapter c.currentBase c.stageBase c.finish
        c.reserved c.query c.geometry c.boundaries c.std hashv call))).2 := by
  cases call <;> simp only [GExq_ChildCode.execute,DrvC_OraclePort.program_liftM]
  all_goals rfl

#print axioms invoke
end AspisR1.SCH_IdealSdkInvoke
end
