import F3U_ReifyValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_ReifyLog
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem log {A : Type} (code : SdkC_Source.Code A) (H : Bytes → State) (before : SdkC_Source.Log) :
    SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H) code before).2=
      SdkC_Source.readLog before++(eval H (SdkC_Oracle.program code)).1 := by
  induction code generalizing before with
  | done value => simp only [SdkC_Source.run,SdkC_Oracle.program,eval,List.append_nil]
  | step result next ih => cases result with
    | fail e => simp only [SdkC_Source.run,SdkC_Oracle.program,eval,List.append_nil]
    | div => simp only [SdkC_Source.run,SdkC_Oracle.program,eval,List.append_nil]
    | ok value => exact ih value before
  | read parts next ih =>
    simp only [SdkC_Source.run,F3U_Oracle.hashv]
    rw [ih]
    simp only [SdkC_Oracle.program,eval,SdkC_Oracle.readLog_append,SdkC_Source.readLog,
      List.filterMap_append,List.filterMap_cons,List.filterMap_nil,F3U_Oracle.decoded,List.append_assoc,List.singleton_append]

#print axioms log
end AspisR1.F3U_ReifyLog
end
