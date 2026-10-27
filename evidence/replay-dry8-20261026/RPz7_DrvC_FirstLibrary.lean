import RPz7_DrvC_OracleNormalize
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstLibrary
open Aeneas Aeneas.Std Result
open DrvC_Installation DrvC_FirstConstants DrvC_OraclePort
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem split {F C : Type} (c : Configuration F C) :
    SdkC_Oracle.program (DrvC_CallCode.code c .op16) = .done (ok 10#usize) := by
  rw [DrvC_CallCode.implementation]
  rfl

theorem mark {F C : Type} (c : Configuration F C) (phase : VTop_Stages.verifier.Phase) :
    SdkC_Oracle.program (DrvC_CallCode.code (configuration c) (.op13 none phase)) = .done (ok ()) := by
  rw [DrvC_CallCode.implementation]
  rfl

theorem folded {F C : Type} (c : Configuration F C) :
    SdkC_Oracle.program (DrvC_CallCode.code c .op15) = .done (ok 7751#usize) := by
  rw [DrvC_CallCode.implementation]
  rfl

theorem round1 {F C : Type} (c : Configuration F C) :
    SdkC_Oracle.program (DrvC_CallCode.code c .op14) = .done (ok 7783#usize) := by
  rw [DrvC_CallCode.implementation]
  rfl

theorem unwrap {F C : Type} (c : Configuration F C)
    (r : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) :
    SdkC_Oracle.program (DrvC_CallCode.code c (.unwrap32 r)) =
      .done (core.result.Result.unwrap core.fmt.DebugTryFromSliceError r) := by
  rw [DrvC_CallCode.implementation]
  cases r <;> rfl

#print axioms split
#print axioms mark
#print axioms folded
#print axioms round1
#print axioms unwrap
end AspisR1.DrvC_FirstLibrary
end
