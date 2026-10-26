import CPH_Game
import SCE_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_GameSelection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

/-- Exact game-field consequence. Shared-adversary input projection alone
cannot supply this entry/bank association. -/
theorem fixed_first {Tx A : Type} (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (e1 e2 : Entry) (saved : alloc.vec.Vec U8) (actions : List (CPP_BankState.Action A))
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions n1 n2 copy allocator id) :
    e1 = CPG_Projection.entry p t := game.consecutive.2.1

/-- The admitted adversary language can response-select DIFFERENT first
entries in two worlds, so fixing one pair of game observations does not
make it a game-indexed factory. This theorem makes no acceptance claim. -/
theorem adaptive_entries {A : Type} (i j : GExq_AccountExperiment.FirstInputs A) :
    ∃ source : AspisV8R19.MemoizedProgramLaw.Program Bytes State (GExq_AccountExperiment.FirstInputs A),
      (eval (fun _ _ => 0) source).2 = i ∧
      (eval (fun _ _ => 1) source).2 = j := by
  let source : AspisV8R19.MemoizedProgramLaw.Program Bytes State (GExq_AccountExperiment.FirstInputs A) :=
    .ask [] (fun answer => .done (if answer 0 = 0 then i else j))
  refine ⟨source,?_,?_⟩
  · simp only [source,eval,ite_true]
  · simp only [source,eval,show (1 : AspisV8R19.DuplexFrames.Byte) ≠ 0 by decide,if_false]

#print axioms fixed_first
#print axioms adaptive_entries
end AspisR1.SCH_GameSelection
end
