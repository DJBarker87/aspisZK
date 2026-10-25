import Hir_Choice
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_FirstChoice
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def input {A : Type} (store : Store) (submission : Call A) : GExq_AccountExperiment.FirstInputs A :=
  ⟨load store submission.layout,submission.data,submission.state⟩

def program {A : Type} (store : Store) (adversary : Program Bytes State (Call A)) :
    Program Bytes State (GExq_AccountExperiment.FirstInputs A) :=
  bind adversary (fun submission => .done (input store submission))

theorem selected {A : Type} (store : Store) (adversary : Program Bytes State (Call A)) (H : Bytes → State) :
    (eval H (program store adversary)).2 = input store (eval H adversary).2 := by
  simp only [program,eval_bind,eval]

theorem charged {A : Type} (store : Store) (adversary : Program Bytes State (Call A)) (H : Bytes → State) :
    (eval H (program store adversary)).1 = (eval H adversary).1 := by
  simp only [program,eval_bind,eval,List.append_nil]

#print axioms selected
#print axioms charged
end AspisR1.Hir_FirstChoice
end
