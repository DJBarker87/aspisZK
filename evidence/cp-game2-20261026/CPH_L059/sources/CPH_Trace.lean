import CPH_Game
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_Trace
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState

variable {Tx A : Type} {p : Observations Tx A} {t u : Tx}
    {e1 e2 : Entry} {saved : alloc.vec.Vec U8} {actions : List (Action A)}
    {n1 : S2W_ExtractionBoundary.First} {n2 : S2W_ExtractionBoundary.Second}
    {copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record)}
    {allocator : Allocator A} {id : S2W_ExtractionBoundary.Program}

def Facts (p : Observations Tx A) (t u : Tx) (saved : alloc.vec.Vec U8)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) : Prop :=
  CPP_BankHistory.run n1 n2 copy allocator id
    (CPR_SourceBank.afterCopy (cached (p.bank t)) ((p.layout t).handles 2).1 saved) (p.actions t) =
      (p.parentTentative t,p.physicalEvents t) ∧
  CPP_BankHistory.run n1 n2 copy allocator id (cached (p.bank u)) (p.actions u) =
      (p.parentTentative u,p.physicalEvents u)

theorem derive (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions n1 n2 copy allocator id) :
    Facts p t u saved n1 n2 copy allocator id := by
  constructor
  · rw [game.recorded.1.2.1]
    exact CPG_RuntimeTrace.result game.recorded.1.2.2
  · exact CPG_RuntimeTrace.result game.recorded.2

#print axioms derive
end AspisR1.CPH_Trace
end
