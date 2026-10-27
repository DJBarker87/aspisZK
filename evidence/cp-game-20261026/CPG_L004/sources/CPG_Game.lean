import CPG_Projection
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPG_Game
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry

/-- Exactly the four clauses of the owner-approved 2026-10-26 game amendment.
This record contains NO persistence/history equality or ordinary eligibility.
The action pair records the actual copy followed by the parent suffix. -/
structure DeployedPairExecution {Tx A : Type} (p : Observations Tx A)
    (t u : Tx) (e1 e2 : Entry) (saved : alloc.vec.Vec U8)
    (sourceActions : List (Action A)) : Prop where
  /-- (a) "the TX1 and TX2 entries are consecutive executions on one bank lineage;" -/
  consecutive : p.next t u ∧ e1 = entry p t ∧ e2 = entry p u
  /-- (b) "both name the same physical verifier checkpoint (CP) account, and no other transaction touches that account between them;" -/
  checkpoint : ((p.layout t).handles 2).1 = ((p.layout u).handles 6).1 ∧
    CPS_PhysicalKey.key e1 2 = CPS_PhysicalKey.key e2 6 ∧
    ((p.layout t).handles 2).1 ∉ p.intervening t u
  /-- (c) "TX1's final parent status is success;" -/
  parent : success p t = true
  /-- (d) "the recorded checkpoint actions are the physical runtime actions of these two transactions." -/
  recorded : p.copied t = saved ∧ p.actions t = sourceActions

theorem next {Tx A : Type} {p : Observations Tx A} {t u : Tx}
    {e1 e2 : Entry} {saved : alloc.vec.Vec U8} {actions : List (Action A)}
    (game : DeployedPairExecution p t u e1 e2 saved actions) : adjacent p t u :=
  ⟨game.consecutive.1,game.checkpoint.2.2⟩

#print axioms next
end AspisR1.CPG_Game
end
