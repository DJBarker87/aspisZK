import ARV_FirstPartial
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARW_Induced
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
variable {A : Type}
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)

/-- Native wrapper computation is pure here. Only the adversary's issued calls
are charged to P. This is a model program, not an executable complexity claim. -/
def program : F3T_ByteCarrier.ByteProver :=
  bind a.first fun i =>
    match first native1 copy allocator i.entry id i.data i.state with
    | .ok (.Ok (saved,post,final)) =>
      bind (a.second i saved post final) fun _ => .done (submitted i)
    | _ => .done (submitted i)

/-- Both reached adversary phases, preserving duplicates and response order. -/
def issued (H : Bytes → State) : List (Bytes × State) :=
  let i := eval H a.first
  i.1 ++ match first native1 copy allocator i.2.entry id i.2.data i.2.state with
    | .ok (.Ok (saved,post,final)) => (eval H (a.second i.2 saved post final)).1
    | _ => []

theorem evaluation (H : Bytes → State) :
    eval H (program native1 copy allocator id a) =
      (issued native1 copy allocator id a H,submitted (eval H a.first).2) := by
  unfold program issued
  simp only [eval_bind]
  split <;> simp only [eval_bind,eval,List.append_nil]

theorem queries (H : Bytes → State) :
    (eval H (program native1 copy allocator id a)).1.length =
      (issued native1 copy allocator id a H).length := by
  rw [evaluation]

theorem output (H : Bytes → State) :
    (eval H (program native1 copy allocator id a)).2 =
      (eval H (submission a)).2 := by
  rw [evaluation,submission_eval]

#print axioms evaluation
#print axioms queries
#print axioms output
end AspisR1.ARW_Induced
end
