import RPz7_DrvC_FirstPrograms
import RPz7_DrvC_FirstConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_OracleNormalize
open Aeneas Aeneas.Std Result
open DrvC_Installation Tx1Q_Carriers DrvC_OraclePort
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult

theorem program_pure {A : Type} (a : A) :
    SdkC_Oracle.program (pure a : SdkC_Source.Code A) = .done (.ok a) := rfl

theorem program_lift {A : Type} (r : Result A) :
    SdkC_Oracle.program (monadLift r : SdkC_Source.Code A) = .done r := by
  exact DrvC_CallCode.program_lift r

theorem bindR_done {A B : Type} (r : Result A) (k : A → Port B) :
    bindR (.done r) k = VTop_OracleCode.continueWith r k := rfl

theorem map_code {A B : Type} (f : A → B) (p : SdkC_Source.Code A) :
    SdkC_Oracle.program (DrvC_Program.mapCode f p) = mapR f (SdkC_Oracle.program p) :=
  DrvC_Program.program_map f p

theorem program_if {A : Type} (p : Prop) [Decidable p] (yes no : SdkC_Source.Code A) :
    SdkC_Oracle.program (if p then yes else no) =
      if p then SdkC_Oracle.program yes else SdkC_Oracle.program no := by split <;> rfl

#print axioms program_pure
#print axioms program_lift
#print axioms bindR_done
#print axioms map_code
#print axioms program_if
end AspisR1.DrvC_OracleNormalize
end
