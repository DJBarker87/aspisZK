import SCH_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_OracleErase
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem result {A : Type} (H : Bytes → State) (code : Code A) :
    CheckpointBytes5Effect.erase (dictionary (SCH_Oracle.ideal H)) () code =
      (eval H (SdkC_Oracle.program code)).2 :=
  (erasure (SCH_Oracle.ideal H) code []).symm.trans (SCH_Oracle.evaluation H code []).1

#print axioms result
end AspisR1.SCH_OracleErase
end
