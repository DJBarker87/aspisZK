import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_CodeEval
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem bind_program {A B : Type} (c : Code A) (k : A → Code B) :
    SdkC_Oracle.program (CheckpointBytes5Effect.bind c k)=
      bind (SdkC_Oracle.program c) (fun r=>match r with
        | ok a=>SdkC_Oracle.program (k a) | fail e=>.done (fail e) | div=>.done div) := by
  induction c with
  | done a=>rfl
  | step r next ih=>cases r <;> first | rfl | exact ih _
  | read parts next ih=>
    simp only [CheckpointBytes5Effect.bind,SdkC_Oracle.program,AspisV8R19.OracleProgramOps.bind]
    congr 1
    funext answer
    exact ih _

theorem bind_eval {A B : Type} (H : Bytes → State) (c : Code A) (k : A → Code B) :
    eval H (SdkC_Oracle.program (CheckpointBytes5Effect.bind c k))=
      let first := eval H (SdkC_Oracle.program c)
      let next := match first.2 with
        | ok a=>eval H (SdkC_Oracle.program (k a)) | fail e=>([],fail e) | div=>([],div)
      (first.1++next.1,next.2) := by
  rw [bind_program,eval_bind]
  dsimp only
  cases h : (eval H (SdkC_Oracle.program c)).2 <;> rfl

theorem lift_eval {A : Type} (H : Bytes → State) (r : Result A) :
    eval H (SdkC_Oracle.program (liftResult r))=([],r) := by cases r <;> rfl

theorem lift_bind_eval {A B : Type} (H : Bytes → State) (r : Result A) (k : A → Code B) :
    eval H (SdkC_Oracle.program (CheckpointBytes5Effect.bind (liftResult r) k))=
      match r with
      | ok a=>eval H (SdkC_Oracle.program (k a)) | fail e=>([],fail e) | div=>([],div) := by
  rw [bind_eval,lift_eval]
  cases r <;> rfl

#print axioms bind_program
#print axioms bind_eval
#print axioms lift_eval
#print axioms lift_bind_eval
end AspisR1.F3Q_CodeEval
end
