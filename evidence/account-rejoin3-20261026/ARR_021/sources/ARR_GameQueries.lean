import CPH_Game
import GExq_AccountExperiment
import GExq_GlobalBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARR_GameQueries
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open GExq_AccountExperiment

/-- Padding is an ordinary oracle program. It does not change any submitted
entry or any physical bank/native witness. Issued repeated calls still cost. -/
def pad {X : Type} (address : Bytes) : Nat → Program Bytes State X → Program Bytes State X
  | 0, p => p
  | n+1, p => .ask address (fun _ => pad address n p)

theorem evaluation {X : Type} (address : Bytes) (n : Nat)
    (p : Program Bytes State X) (H : Bytes → State) :
    eval H (pad address n p) =
      (List.replicate n (address,H address) ++ (eval H p).1,(eval H p).2) := by
  induction n with
  | zero => simp only [pad,List.replicate_zero,List.nil_append]
  | succ n ih => simp only [pad,eval,ih,List.replicate_succ,List.cons_append]

theorem selected {X : Type} (address : Bytes) (n : Nat)
    (p : Program Bytes State X) (H : Bytes → State) :
    (eval H (pad address n p)).2 = (eval H p).2 := by rw [evaluation]

theorem queries {X : Type} (address : Bytes) (n : Nat)
    (p : Program Bytes State X) (H : Bytes → State) :
    (eval H (pad address n p)).1.length = n+(eval H p).1.length := by
  rw [evaluation,List.length_append,List.length_replicate]

/-- The exact approved game admits EVERY amount of ignored query padding
before the second entry is selected, whenever it admits the original entry.
This proves no blanket no-adaptive-queries restriction follows from game a-d. -/
theorem game_iff {Tx A : Type} (p : CPG_Projection.Observations Tx A)
    (t u : Tx) (e1 : Entry) (saved : alloc.vec.Vec U8) (actions : List (CPP_BankState.Action A))
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (choice : Program Bytes State (SecondInputs A)) (H : Bytes → State) (address : Bytes) (n : Nat) :
    CPH_Game.DeployedPairExecution p t u e1 (eval H (pad address n choice)).2.entry
      saved actions n1 n2 copy allocator id ↔
    CPH_Game.DeployedPairExecution p t u e1 (eval H choice).2.entry
      saved actions n1 n2 copy allocator id := by rw [selected]

/-- Rejection as well as success is identical at the second native wrapper;
the original state, slot, data, allocator and error are all retained. -/
theorem native_second {A : Type} (native : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (choice : Program Bytes State (SecondInputs A)) (H : Bytes → State) (address : Bytes) (n : Nat) :
    let j := (eval H (pad address n choice)).2
    let k := (eval H choice).2
    second native allocator j.entry id j.data j.slot j.state =
      second native allocator k.entry id k.data k.slot k.state := by
  dsimp only
  rw [selected]

#print axioms evaluation
#print axioms selected
#print axioms queries
#print axioms game_iff
#print axioms native_second
end AspisR1.ARR_GameQueries
end
