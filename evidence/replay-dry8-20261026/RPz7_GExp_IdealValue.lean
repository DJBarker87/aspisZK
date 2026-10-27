import RPz7_GExp_NodeBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_IdealValue
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

def dictionary (H : Bytes → State) :=
  SdkC_Source.dictionary (fun parts => ok (encodeState (H (flatten parts))))

theorem value {A : Type} (H : Bytes → State) (code : Code A) :
    (eval H (SdkC_Oracle.program code)).2 = erase (dictionary H) () code := by
  induction code with
  | done a => rfl
  | step r k ih => cases r <;> first | rfl | exact ih _
  | read parts k ih => exact ih _

theorem bind_program {A B : Type} (p : Code A) (k : A → Code B) :
    SdkC_Oracle.program (CheckpointBytes5Effect.bind p k) =
      AspisV8R19.OracleProgramOps.bind (SdkC_Oracle.program p) (fun r => match r with
        | .ok a => SdkC_Oracle.program (k a)
        | .fail e => .done (.fail e)
        | .div => .done .div) := by
  induction p with
  | done a => rfl
  | step r c ih => cases r <;> first | rfl | exact ih _
  | read parts c ih =>
    simp only [CheckpointBytes5Effect.bind,SdkC_Oracle.program,AspisV8R19.OracleProgramOps.bind]
    congr 1
    funext reply
    exact ih _

#print axioms value
#print axioms bind_program
end AspisR1.GExp_IdealValue
end
