import DrvC_Implementation
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_CallCode
open Aeneas Aeneas.Std Result
open DrvC_Installation DrvC_Carriers Tx1Q_Carriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def code {F C A : Type} (c : Configuration F C) : VTop_Trace.Call A → SdkC_Source.Code A
  | .op5 D proof p root which hash =>
      SdkC_BatchSource.mapCode Op5T_Install.stageError
        (SdkC_BatchSource.code (VTop_Checkpoint.digest D) hash proof p.queries p.roots root which)
  | .op7 D pub proof hash obs scratch =>
      match obs with
      | none => DrvC_Implementation.prepare c D pub proof hash scratch
      | some observer => CheckpointBytes5Effect.liftResult
          ((DrvC_Dictionary.ops c).op7 D pub proof hash (some observer) scratch)
  | .op8 _ p a proof pub _ =>
      GExp_FirstCode.writerCode (unPrepared p) (unAccumulator a) proof pub
  | .op18 _ ck proof pub v _ => GExp_RetainedReader.code c.reserved ck proof pub v
  | op => CheckpointBytes5Effect.liftResult (VTop_Trace.invoke (DrvC_Dictionary.ops c) op)

theorem program_lift {A : Type} (r : Result A) :
    SdkC_Oracle.program (CheckpointBytes5Effect.liftResult r) = .done r := by cases r <;> rfl

theorem implementation {F C A : Type} (c : Configuration F C) (call : VTop_Trace.Call A) :
    SdkC_Oracle.program (code c call) = DrvC_Implementation.implementation c call := by
  cases call <;> first
    | rfl
    | exact program_lift _
    | (rename_i obs scratch; cases obs <;> first | rfl | exact program_lift _)

/-- The typed source call tree lowered into the same literal digest syntax. -/
def lower {F C A : Type} (c : Configuration F C) : VTop_Trace.Code A → SdkC_Source.Code A
  | .done a => .done a
  | .step r k => .step r (fun a => lower c (k a))
  | .call op k => CheckpointBytes5Effect.bind (code c op) (fun a => lower c (k a))

theorem program_bind {A B : Type} (p : SdkC_Source.Code A) (k : A → SdkC_Source.Code B) :
    SdkC_Oracle.program (CheckpointBytes5Effect.bind p k) =
      bind (SdkC_Oracle.program p) (fun r => VTop_OracleCode.continueWith r
        (fun a => SdkC_Oracle.program (k a))) := by
  induction p with
  | done a => rfl
  | step r next ih => cases r with
    | ok a => exact ih a
    | fail e => rfl
    | div => rfl
  | read parts next ih =>
    simp only [CheckpointBytes5Effect.bind,SdkC_Oracle.program,AspisV8R19.OracleProgramOps.bind]
    congr 1
    funext answer
    exact ih _

theorem program_lower {F C A : Type} (c : Configuration F C) (tree : VTop_Trace.Code A) :
    SdkC_Oracle.program (lower c tree) =
      VTop_OracleCode.interpret (DrvC_Implementation.implementation c) tree := by
  induction tree with
  | done a => rfl
  | step r k ih => cases r with
    | ok a => exact ih a
    | fail e => rfl
    | div => rfl
  | call op k ih =>
    rw [lower,program_bind,implementation]
    congr 1
    funext r
    cases r with
    | ok a => exact ih a
    | fail e => rfl
    | div => rfl

#print axioms program_lift
#print axioms implementation
#print axioms program_bind
#print axioms program_lower
end AspisR1.DrvC_CallCode
end
