import SCE_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_IdealSdk
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Oracle-indexed interpreter for the two verifier children. This dictionary
is an inspection device, not an asserted native implementation. -/
def dictionary {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State) : AdapterRw.Ops :=
  { DrvC_Installation.sdk c with
    op10 := fun D semantic pub proof split hash obs =>
      (eval H (SdkC_Oracle.program (GExq_ChildCode.execute c.adapter c.currentBase c.stageBase c.finish
        c.reserved c.query c.geometry c.boundaries c.std hashv
        (.op10 D semantic pub proof split hash obs)))).2
    op11 := fun D pub proof checkpoint hash obs =>
      (eval H (SdkC_Oracle.program (GExq_ChildCode.execute c.adapter c.currentBase c.stageBase c.finish
        c.reserved c.query c.geometry c.boundaries c.std hashv
        (.op11 D pub proof checkpoint hash obs)))).2 }

theorem invoke {F C A : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (call : S2W_Trace.Call A) :
    S2W_Trace.invoke (dictionary c hashv H) call =
      (eval H (SdkC_Oracle.program (GExq_ChildCode.execute c.adapter c.currentBase c.stageBase c.finish
        c.reserved c.query c.geometry c.boundaries c.std hashv call))).2 := by
  cases call <;> first | rfl | (simp only [GExq_ChildCode.execute,DrvC_OraclePort.program_liftM]; rfl)

#print axioms invoke
end AspisR1.SCH_IdealSdk
end
