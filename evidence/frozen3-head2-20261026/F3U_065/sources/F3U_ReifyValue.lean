import F3U_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_ReifyValue
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem value {A : Type} (code : SdkC_Source.Code A) (H : Bytes → State) :
    (eval H (SdkC_Oracle.program code)).2=
      CheckpointBytes5Effect.erase (SdkC_Source.dictionary (F3U_Oracle.hashv H)) () code := by
  induction code with
  | done value => rfl
  | step result next ih => cases result with
    | fail e => rfl
    | div => rfl
    | ok value => exact ih value
  | read parts next ih =>
    simp only [SdkC_Oracle.program,eval,CheckpointBytes5Effect.erase,SdkC_Source.dictionary,F3U_Oracle.hashv,bind_tc_ok]
    exact ih _

#print axioms value
end AspisR1.F3U_ReifyValue
end
