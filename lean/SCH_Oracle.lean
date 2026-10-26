import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_Oracle
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

/-- Total interpretation used only to inspect the ideal program. This is not
an identification of the retained, potentially failing runtime syscall. -/
def ideal (H : Bytes → State) (parts : Parts) : Result Digest :=
  ok (encodeState (H (flatten parts)))

theorem evaluation {A : Type} (H : Bytes → State) (code : Code A) (before : Log) :
    (run (ideal H) code before).1 = (eval H (SdkC_Oracle.program code)).2 ∧
    readLog (run (ideal H) code before).2 =
      readLog before ++ (eval H (SdkC_Oracle.program code)).1 := by
  induction code generalizing before with
  | done a => exact ⟨rfl,(List.append_nil _).symm⟩
  | step r k ih =>
    cases r with
    | fail e => exact ⟨rfl,(List.append_nil _).symm⟩
    | div => exact ⟨rfl,(List.append_nil _).symm⟩
    | ok a => exact ih a before
  | read parts k ih =>
    obtain ⟨result,log⟩ := ih (encodeState (H (flatten parts)))
      (before ++ [⟨parts,ok (encodeState (H (flatten parts)))⟩])
    simp only [run,ideal,SdkC_Oracle.program,eval]
    refine ⟨result,?_⟩
    rw [log,SdkC_Oracle.readLog_append]
    simp only [readLog,List.filterMap_cons,List.filterMap_nil,List.append_nil,
      state_roundtrip,SdkC_Oracle.program,eval,List.append_assoc,List.singleton_append]

#print axioms evaluation
end AspisR1.SCH_Oracle
end
