import DrvC_MapCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_CodeMap
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Result conversion does not change any successful or rejected source read. -/
theorem log {A B : Type} (f : A → B) (code : SdkC_Source.Code A)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    SdkC_Source.readLog (SdkC_Source.run hashv
      (CheckpointBytes5Effect.bind code (fun a => .done (f a))) []).2 =
      SdkC_Source.readLog (SdkC_Source.run hashv code []).2 := by
  rw [← DrvC_MapCode.map_as_bind]
  rw [DrvC_Program.mapCode_source]

/-- The same fact on the ideal oracle program, on every outcome. -/
theorem ideal_log {A B : Type} (f : A → B) (code : SdkC_Source.Code A) (H : Bytes → State) :
    (eval H (SdkC_Oracle.program
      (CheckpointBytes5Effect.bind code (fun a => .done (f a))))).1 =
      (eval H (SdkC_Oracle.program code)).1 := by
  rw [← DrvC_MapCode.map_as_bind,DrvC_Program.program_map,DrvC_Program.eval_map]

#print axioms log
#print axioms ideal_log
end AspisR1.SCG_CodeMap
end
