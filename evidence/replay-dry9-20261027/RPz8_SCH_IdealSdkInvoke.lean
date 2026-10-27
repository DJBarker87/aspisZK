import RPz8_SCH_IdealSdk
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
  unfold SCH_IdealSdk.dictionary
  cases call <;> simp only [S2W_Trace.invoke]
  all_goals unfold GExq_ChildCode.execute
  all_goals first | rfl | (rw [show ∀ {B : Type} (r : Result B),
    SdkC_Oracle.program (CheckpointBytes5Effect.liftResult r) = .done r from
      fun r => by cases r <;> rfl]; rfl)

#print axioms invoke
end AspisR1.SCH_IdealSdkInvoke
end
