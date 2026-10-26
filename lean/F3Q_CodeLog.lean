import F3Q_CodeEval
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_CodeLog
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem lift_tail {A B : Type} (H : Bytes → State) (c : Code A) (k : A → Result B) :
    (eval H (SdkC_Oracle.program (CheckpointBytes5Effect.bind c (fun a=>liftResult (k a))))).1=
      (eval H (SdkC_Oracle.program c)).1 := by
  rw [F3Q_CodeEval.bind_eval]
  dsimp only
  cases h : (eval H (SdkC_Oracle.program c)).2 <;>
    simp only [F3Q_CodeEval.lift_eval,List.append_nil]

theorem done_tail {A B : Type} (H : Bytes → State) (c : Code A) (k : A → B) :
    (eval H (SdkC_Oracle.program (CheckpointBytes5Effect.bind c (fun a=>.done (k a))))).1=
      (eval H (SdkC_Oracle.program c)).1 := by
  rw [F3Q_CodeEval.bind_eval]
  dsimp only
  cases h : (eval H (SdkC_Oracle.program c)).2 <;>
    simp only [SdkC_Oracle.program,eval,List.append_nil]

#print axioms lift_tail
#print axioms done_tail
end AspisR1.F3Q_CodeLog
end
