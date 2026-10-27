import R1Z.PV_RunJoin_LedgerHistory
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerStrict
open ProverCommitLedger36

/-- Every entered reserve records at least the create outcome, including a
duplicate or IO failure. Thus unchanged source handles cannot encode even
the exact event history, independently of fresh-path membership. -/
theorem reserve_history_strict (schedule : Schedule) (unix : Bool) (path : Path) (s : State) :
    s.history.length < (reserve schedule unix path s).2.history.length := by
  have created := PV_RunJoin_LedgerHistory.create_length path
    (schedule s.history.length .create s.history) s
  cases outcome : (createNew path (schedule s.history.length .create s.history) s).1 with
  | error error =>
    cases error <;> simp only [reserve,outcome]
    all_goals omega
  | ok value =>
    have after := PV_RunJoin_LedgerHistory.chain_length_ge schedule
      (ProverCommitEnvironment35.writes unix)
      (createNew path (schedule s.history.length .create s.history) s).2
    rcases chain : ioChain schedule (ProverCommitEnvironment35.writes unix)
      (createNew path (schedule s.history.length .create s.history) s).2 with ⟨status,final⟩
    rw [chain] at after
    dsimp only at after
    simp only [reserve,outcome,chain]
    omega

theorem reserve_ne (schedule : Schedule) (unix : Bool) (path : Path) (s : State) :
    (reserve schedule unix path s).2 ≠ s := by
  intro same
  have strict := reserve_history_strict schedule unix path s
  rw [same] at strict
  exact Nat.lt_irrefl _ strict

#print axioms reserve_history_strict
#print axioms reserve_ne
end R1Z.PV_RunJoin_LedgerStrict
